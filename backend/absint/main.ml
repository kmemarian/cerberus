open Cerb_frontend
open Cerb_backend
open Cerb_global
open Pipeline

let (>>=) = Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = Exception.except_return

let io, get_progress =
  let open Pipeline in
  default_io_helpers, get_progress

let frontend (conf, io) filename core_std =
  if not (Sys.file_exists filename) then
    error ("The file `" ^ filename ^ "' doesn't exist.");
  if Filename.check_suffix filename ".co" || Filename.check_suffix filename ".o" then
    return @@ read_core_object core_std filename
  else if Filename.check_suffix filename ".c" then
    c_frontend_and_elaboration (conf, io) core_std ~filename >>= fun (_, _, core_file) ->
    core_passes (conf, io) ~filename core_file
  else if Filename.check_suffix filename ".core" then
    core_frontend (conf, io) core_std ~filename
    >>= core_passes (conf, io) ~filename
  else
    Exception.fail (Cerb_location.unknown, Errors.UNSUPPORTED
                      "The file extention is not supported")

let create_cpp_cmd cpp_cmd nostdinc macros_def macros_undef incl_dirs incl_files nolibc =
  let libc_dirs = Cerb_runtime.[in_runtime "bmc"; in_runtime "libc/include"; in_runtime "libc/include/posix"] in
  let incl_dirs = if nostdinc then incl_dirs else libc_dirs @ incl_dirs in
  let macros_def = if nolibc then macros_def else ("CERB_WITH_LIB", None) :: macros_def in
  String.concat " " begin
    cpp_cmd ::
    List.map (function
        | (str1, None)      -> "-D" ^ str1
        | (str1, Some str2) -> "-D" ^ str1 ^ "=" ^ str2
      ) macros_def @
    List.map (fun str -> "-U" ^ str) macros_undef @
    List.map (fun str -> "-I" ^ str) incl_dirs @
    List.map (fun str -> "-include " ^ str) incl_files
  end

let core_libraries incl lib_paths libs =
  let lib_paths = if incl then Cerb_runtime.in_runtime "libc" :: lib_paths else lib_paths in
  let libs = if incl then "c" :: libs else libs in
  List.map (fun lib ->
      match List.fold_left (fun acc path ->
          match acc with
          | Some _ -> acc
          | None ->
            let file = path ^ "/lib" ^ lib ^ ".co" in
            if Sys.file_exists file then Some file else None
        ) None lib_paths with
      | Some f -> f
      | None -> failwith @@ "file lib" ^ lib ^ ".co not found"
    ) libs

let print_file f =
  let ic = open_in f in
  let rec loop () =
    try print_endline @@ input_line ic; loop ()
    with End_of_file -> ()
  in loop ()

let create_executable out =
  let out = if Filename.is_relative out then Filename.concat (Unix.getcwd ()) out else out in
  let oc = open_out out in
  output_string oc "#!/bin/sh\n";
  output_string oc @@ "cerberus --nolibc --exec " ^ out ^ ".co\n";
  close_out oc;
  Unix.chmod out 0o755

let cerberus debug_level progress
             cpp_cmd nostdinc nolibc macros macros_undef
             incl_dirs incl_files cpp_only
             link_lib_path link_core_obj
             impl_name
             switches
             cfg absdomain
             astprints pprints ppflags
             sequentialise_core rewrite_core typecheck_core defacto
             fs_dump fs
             output_name
             files args_opt =
  Cerb_debug.debug_level := debug_level;
  let cpp_cmd =
    create_cpp_cmd cpp_cmd nostdinc macros macros_undef incl_dirs incl_files nolibc
  in
  (*
  let args = match args_opt with
    | None -> []
    | Some args -> Str.split (Str.regexp "[ \t]+") args
  in *)
  (* set global configuration *)
  set_cerb_conf "Absint" false Random false QuoteStd defacto false false false;
  let conf = { astprints; pprints; ppflags; debug_level; typecheck_core;
               rewrite_core; sequentialise_core; cpp_cmd; cpp_stderr = true } in
  let prelude =
    (* Looking for and parsing the core standard library *)
    Switches.set switches;
    load_core_stdlib () >>= fun core_stdlib ->
    io.pass_message "Core standard library loaded." >>
    (* Looking for and parsing the implementation file *)
    load_core_impl core_stdlib impl_name >>= fun core_impl ->
    io.pass_message "Implementation file loaded." >>
    return (core_stdlib, core_impl)
  in
  let main core_std =
    Exception.except_foldlM (fun core_files file ->
        frontend (conf, io) file core_std >>= fun core_file ->
        return (core_file::core_files)) [] (core_libraries (not nolibc) link_lib_path link_core_obj @ files)
  in
  let epilogue n =
    if progress then get_progress ()
    else n
  in
  let success = Either.Right 0 in
  let runM = function
    | Exception.Exception err ->
        prerr_endline (Pp_errors.to_string err);
        epilogue 1
    | Exception.Result (Either.Left execs) ->
        List.iter print_string execs;
        epilogue 0
    | Exception.Result (Either.Right n) ->
        epilogue n
  in
  runM @@ match files with
    | [] ->
      Pp_errors.fatal "no input file"
    | first_file::tail_files as files ->
      (* Run only CPP *)
      let output_filename =
        match output_name with
        | Some name -> name
        | None -> Filename.chop_extension first_file
      in
      if cpp_only then
        Exception.except_foldlM (fun () filename ->
            cpp (conf, io) ~filename >>= fun processed_file ->
            print_file processed_file;
            return ()
          ) () files >>= fun () ->
        return success
      (* Link and execute *)
      else
        prelude >>= main >>= begin function
          | [] -> assert false
          | f::fs -> Core_linking.link (f::fs)
        end >>= fun core ->
        if cfg then
          Cfg.mk_dot ~sequentialise:sequentialise_core output_filename core;
        typed_core_passes (conf, io) core >>= fun (core, _) ->
        ignore (Absint.solve output_filename absdomain core);
        return success

(* CLI stuff *)
open Cmdliner

let macro_pair =
  let parser str =
    match String.index_opt str '=' with
      | None ->
          Result.Ok (str, None)
      | Some i ->
          let macro = String.sub str 0 i in
          let value = String.sub str (i+1) (String.length str - i - 1) in
          let is_digit n = 48 <= n && n <= 57 in
          if i = 0 || is_digit (Char.code (String.get macro 0)) then
            Result.Error (`Msg "macro name must be a C identifier")
          else
            Result.Ok (macro, Some value) in
  let printer ppf = function
    | (m, None)   -> Format.pp_print_string ppf m
    | (m, Some v) -> Format.fprintf ppf "%s=%s" m v in
  Arg.(conv (parser, printer))

let debug_level =
  let doc = "Set the debug message level to $(docv) (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let impl =
  let doc = "Set the C implementation file (to be found in CERB_COREPATH/impls\
             and excluding the .impl suffix)." in
  Arg.(value & opt string "gcc_4.9.0_x86_64-apple-darwin10.8.0" & info ["impl"]
         ~docv:"NAME" ~doc)

let link_lib_path =
  let doc = "Adds a new library search path." in
  Arg.(value & opt_all string [] & info ["L"] ~docv:"X" ~doc)

let link_core_obj =
  let doc = "This option tells the core linker to search for lib$(docv).co \
             in the library search path." in
  Arg.(value & opt_all string [] & info ["l"] ~docv:"X" ~doc)

let output_file =
  let doc = "Write output to file." in
  Arg.(value & opt (some string) None & info ["o"] ~doc)

let cpp_cmd =
  let doc = "Command to call for the C preprocessing." in
  Arg.(value & opt string ("cc -std=c11 -E -C -Werror -nostdinc -undef -D__cerb__")
             & info ["cpp"] ~docv:"CMD" ~doc)

let cpp_only =
  let doc = "Run only the preprocessor stage." in
  Arg.(value & flag & info ["E"] ~doc)

let incl_dir =
  let doc = "Add the specified directory to the search path for the\
             C preprocessor." in
  Arg.(value & opt_all dir [] & info ["I"; "include-directory"]
         ~docv:"DIR" ~doc)

let macros =
  let doc = "Adds  an  implicit  #define  into the predefines buffer which is \
             read before the source file is preprocessed." in
  Arg.(value & opt_all macro_pair [] & info ["D"; "define-macro"]
         ~docv:"NAME[=VALUE]" ~doc)

let macros_undef =
  let doc = "Adds an implicit #undef into the predefines buffer which is read \
             before the source file is preprocessed." in
  Arg.(value & opt_all string [] & info ["U"] ~doc)

let incl_file =
  let doc = "Adds  an  implicit  #include into the predefines buffer which is \
             read before the source file is preprocessed." in
  Arg.(value & opt_all string [] & info ["include"] ~doc)

let nostdinc =
  let doc = "Do not search includes in the standard lib C directories." in
  Arg.(value & flag & info ["nostdinc"] ~doc)

let nolibc =
  let doc = "Do not search the standard system directories for include files." in
  Arg.(value & flag & info ["nolibc"] ~doc)

let pprints =
  let open Pipeline in
  let doc = "Pretty print the intermediate programs for the listed languages\
             (ranging over {ail, core})." in
  Arg.(value & opt (list (enum ["ail", Ail; "core", Core])) [] &
       info ["pp"] ~docv:"LANG1,..." ~doc)

let astprints =
  let open Pipeline in
  let doc = "Pretty print the intermediate syntax tree for the listed languages\
             (ranging over {cabs, ail, core})." in
  Arg.(value & opt (list (enum ["cabs", Cabs; "ail", Ail])) [] &
       info ["ast"] ~docv:"LANG1,..." ~doc)

let fs =
  let doc = "Initialise the internal file system with the contents of the\
             directory DIR" in
  Arg.(value & opt (some string) None & info ["fs"] ~docv:"DIR" ~doc)

let ppflags =
  let open Pipeline in
  let doc = "Pretty print flags [annot: include location and ISO annotations,\
             fout: output in a file]." in
  Arg.(value & opt (list (enum ["annot", Annot; "fout", FOut])) [] &
       info ["pp_flags"] ~doc)

let files =
  let doc = "source C or Core file" in
  Arg.(value & pos_all file [] & info [] ~docv:"FILE" ~doc)

let progress =
  let doc = "Progress mode: the return code indicate how far the source program\
             went through the pipeline \
             [1 = total failure, 10 = parsed, 11 = desugared, 12 = typed,\
             13 = elaborated, 14 = executed]" in
  Arg.(value & flag & info ["progress"] ~doc)

let rewrite =
  let doc = "Activate the Core to Core transformations" in
  Arg.(value & flag & info["rewrite"] ~doc)

let sequentialise =
  let doc = "Replace all unseq() with left to right wseq(s)" in
  Arg.(value & flag & info["sequentialise"] ~doc)

let typecheck_core =
  let doc = "typecheck the elaborated Core program" in
  Arg.(value & flag & info["typecheck-core"] ~doc)

let defacto =
  let doc = "relax some of the ISO constraints (outside of the memory)" in
  Arg.(value & flag & info["defacto"] ~doc)

let fs_dump =
  let doc = "dump the file system at the end of the execution" in
  Arg.(value & flag & info["fs-dump"] ~doc)

let switches =
  let doc = "list of semantics switches to turn on (see documentation for the list)" in
  Arg.(value & opt (list string) [] & info ["switches"] ~docv:"SWITCH1,..." ~doc)

let args =
  let doc = "List of arguments for the C program" in
  Arg.(value & opt (some string) None & info ["args"] ~docv:"ARG1,..." ~doc)

let cfg =
  let doc = "outputs a dot file with the control flow graph for core" in
  Arg.(value & flag & info["cfg"] ~doc)

let absdomain =
  let doc = "Choose abstract domain (ranging over {box, oct, polka_loose (default), polka_strict, polka_eq})." in
  Arg.(value & opt (enum [("box", `Box);
                          ("oct", `Oct);
                          ("polka_loose", `PolkaLoose);
                          ("polka_strict", `PolkaStrict);
                          ("polka_eq", `PolkaEq)])
         `PolkaLoose & info ["absdomain"] ~doc)


(* entry point *)
let () =
  let cerberus_t = Term.(const cerberus $ debug_level $ progress $
                         cpp_cmd $ nostdinc $ nolibc $ macros $ macros_undef $
                         incl_dir $ incl_file $ cpp_only $
                         link_lib_path $ link_core_obj $
                         impl $
                         switches $
                         cfg $ absdomain $
                         astprints $ pprints $ ppflags $
                         sequentialise $ rewrite $ typecheck_core $ defacto $
                         fs_dump $ fs $
                         output_file $
                         files $ args) in
  let version = Version.version in
  let info = Cmd.info "cerberus" ~version ~doc:"Cerberus C semantics"  in
  Stdlib.exit @@ Cmd.eval' (Cmd.v info cerberus_t)
