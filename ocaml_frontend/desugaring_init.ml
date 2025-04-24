open Monomorphic.None
open Cabs
open Ctype
open Cabs_to_ail_aux

let equal_ctype = Ctype.ctypeEqual

module Symbol = struct
  include Symbol
  let equal_identifier = instance_Basic_classes_Eq_Symbol_identifier_dict.isEqual_method
  let compare_identifier = instance_Basic_classes_SetType_Symbol_identifier_dict.setElemCompare_method
end

module Loc = struct
  let locOf_cabs_expr (CabsExpression (loc, _)) = loc
  let locOf_ail_expr (AilSyntax.AnnotatedExpression (_, _, loc, _)) = loc
  let locOf_identifier (Symbol.Identifier (loc, _)) = loc
end


type init_cursor_kind =
  | Init_array of Z.t(* current index*) * Z.t option(* size (nothing if we are dealing with a top-level unknown sized array) *)
  | Init_struct of Symbol.sym * (Symbol.identifier * ctype) list * Symbol.identifier * (Symbol.identifier * ctype) list
  | Init_union of Symbol.sym * Symbol.identifier
[@@deriving eq]

type init_cursor_elem = {
  is_block: bool; (* indicates whether an Init_list was entered *)
  is_overflowing: bool; (* indicates whether the cursor has overflowed (the current struct or array) *)
  kind: init_cursor_kind;
} [@@deriving eq]

type init_position = {
  block_ty: ctype [@warning "-69"]; (* type of the current { .. } *)
  ty: ctype; (* type at the cursor *)
  cursor: init_cursor_elem list;
  in_block: bool [@warning "-69"];
}

let _mark_as_overflowing pos =
  let cursor =
    match pos.cursor with
      | elem :: cursor' ->
          { elem with is_overflowing= true } :: cursor'
      | z -> z in
  { pos with cursor= cursor }

let unmark_as_overflowing pos =
  let cursor =
    match pos.cursor with
      | elem :: cursor' ->
          { elem with is_overflowing= false } :: cursor'
      | z -> z in
  { pos with cursor= cursor }

let cursor_overflowing = function
  | [] ->
      false
  | elem :: _ ->
      elem.is_overflowing

let lookup_struct_members tagDefs tag_sym =
  let aux (ident, (_, _, _, ty)) = (ident, ty) in
  match Pmap.lookup tag_sym tagDefs with
    | Some (Struct_definition (_, _, _, x::xs, flex_opt)) ->
        (aux x, List.map aux xs, flex_opt)
    | _ ->
        Cerb_debug.error "Desugaring_init.lookup_struct_members: None or empty Struct definition"

let lookup_union_members tagDefs tag_sym =
  let aux (ident, (_, _, _, ty)) = (ident, ty) in
  match Pmap.lookup tag_sym tagDefs with
    | Some (Union_definition (_, _, _, x::xs)) ->
        (aux x, List.map aux xs)
    | _ ->
        Cerb_debug.error "Desugaring_init.lookup_union_members: None or empty Union definition"

let go_down_aux tagDefs entering_block pos =
  if cursor_overflowing pos.cursor then
    (* OVERFLOWING *)
    None
  else
    let mk_cursor_elem kind =
      { is_block= entering_block; is_overflowing= false; kind= kind } in
    match unatomic pos.ty with
      | Ctype (_, Basic _) ->
          None
      | Ctype (_, Pointer _) ->
          None
      | Ctype (_, Array (elem_ty, size_opt)) ->
          Some { pos with ty= elem_ty; cursor= mk_cursor_elem (Init_array (Z.zero, size_opt)) :: pos.cursor }
      | Ctype (_, Struct tag_sym) ->
          let ((first_ident, first_ty), other_membrs, _) = lookup_struct_members tagDefs tag_sym in
          Some { pos with ty= first_ty; cursor= mk_cursor_elem (Init_struct (tag_sym, [], first_ident, other_membrs)) :: pos.cursor }
      | Ctype (_, Union tag_sym) ->
          let ((first_ident, first_ty), _) = lookup_union_members tagDefs tag_sym in
          Some { pos with ty= first_ty; cursor= mk_cursor_elem (Init_union (tag_sym, first_ident)) :: pos.cursor }
      | _ ->
          let ty_str = String_ail.string_of_ctype_human no_qualifiers pos.ty in
          Cerb_debug.error ("Desugaring_init.go_down_aux NOT Basic, Array, Struct, Union ==> " ^ ty_str)

let go_down                tagDefs pos = go_down_aux tagDefs false pos
let go_down_entering_block tagDefs pos = go_down_aux tagDefs true  pos

let rec go_bottom tagDefs pos =
  match go_down tagDefs pos with
    | Some pos ->
        go_bottom tagDefs pos
    | None ->
        pos


let go_up_aux stop_at_block pos =
  match pos.cursor with
    | [] ->
        None
    | elem :: cursor' ->
        begin match elem.kind with
          | Init_array (_, size_opt) ->
              if stop_at_block && elem.is_block then
                None
              else
                Some { pos with ty= Ctype ([], Array (pos.ty, size_opt)); cursor= cursor'}
          | Init_struct (tag_sym, _, _, _) ->
              if stop_at_block && elem.is_block then
                None
              else
                Some { pos with ty= Ctype ([], Struct tag_sym); cursor= cursor' }
          | Init_union (tag_sym, _) ->
              if stop_at_block && elem.is_block then
                None
              else
                Some { pos with ty= Ctype ([], Union tag_sym); cursor= cursor' }
        end

let go_up               pos = go_up_aux false pos
let go_up_stop_at_block pos = go_up_aux true  pos


let rec go_next_aux tagDefs going_up pos =
  if cursor_overflowing pos.cursor then
    (* TODO: check (OVERFLOWING) *)
    None
  else match pos.cursor with
    | [] ->
        go_down tagDefs pos
    | elem :: cursor' ->
        begin match elem.kind with
          | Init_array (current_idx, size_opt) ->
              let new_idx = Z.succ current_idx in
              let index_is_overflowing =
                match size_opt with
                  | Some size -> Z.geq new_idx size
                  | None      -> false in
              if index_is_overflowing then
                if elem.is_block then
                  (* OVERFLOWING *)
                  Some { pos with cursor= { elem with is_overflowing= true } :: cursor' }
                else
                  Option.bind (go_up pos) (go_next_going_up tagDefs)
              else if AilTypesAux.is_scalar (unatomic pos.ty) || going_up then
                Some { pos with cursor= { is_block= elem.is_block; is_overflowing= elem.is_overflowing; kind= Init_array (new_idx, size_opt) } :: cursor' }
              else
                Option.bind (go_down tagDefs pos) (go_next tagDefs)
          | Init_struct (_, _, _, []) ->
              if elem.is_block then
                (* OVERFLOWING *)
                Some { pos with cursor= { elem with is_overflowing= true } :: cursor' }
              else
                Option.bind (go_up pos) (go_next_going_up tagDefs)
          | Init_struct (tag_sym, prev_membrs, current_member, next_membrs) ->
              let (memb_ident, memb_ty) = List.hd next_membrs in
              if AilTypesAux.is_scalar (unatomic pos.ty) || going_up then
                Some { pos with ty= memb_ty; cursor= { elem with kind=
                  Init_struct (tag_sym, prev_membrs @ [(current_member, pos.ty)], memb_ident, List.tl next_membrs) } :: cursor' }
              else
                Option.bind (go_down tagDefs pos) (go_next tagDefs)
          | Init_union _ ->
              if elem.is_block then
                (* OVERFLOWING *)
                Some { pos with cursor= { elem with is_overflowing= true } :: cursor' }
              else
                Option.bind (go_up pos) (go_next_going_up tagDefs)
        end

and go_next          tagDefs pos = go_next_aux tagDefs false pos
and go_next_going_up tagDefs pos = go_next_aux tagDefs true  pos


let do_next_in_same_level tagDefs pos =
  if cursor_overflowing pos.cursor then
    Some pos
  else match pos.cursor with
    | elem :: cursor' ->
        begin match elem.kind with
          | Init_array (current_idx, size_opt) ->
              let new_idx = Z.succ current_idx in
              let index_is_overflowing =
                match size_opt with
                  | Some size -> Z.geq new_idx size
                  | None      -> false in
              if index_is_overflowing then
                if List.is_empty cursor' then
                  (* OVERFLOWING *)
                  Some { pos with cursor= { elem with is_overflowing= true } :: cursor' }
                else
                  Option.bind (go_up pos) (go_next_going_up tagDefs)
              else
                Some { pos with cursor= { elem with kind= Init_array (new_idx, size_opt) } :: cursor' }
          | Init_struct (_, _, _, []) ->
              if List.is_empty cursor' then
                (* OVERFLOWING *)
                Some { pos with cursor= [{ elem with is_overflowing= true }] }
              else
                Option.bind (go_up pos) (go_next_going_up tagDefs)
          | Init_struct (tag_sym, prev_membrs, current_member, (memb_ident, memb_ty) :: next_membrs) ->
              Some ({ pos with ty= memb_ty; cursor= { elem with kind= Init_struct (tag_sym, prev_membrs @ [(current_member, pos.ty)], memb_ident, next_membrs) } :: cursor' })
          | Init_union _ ->
              if List.is_empty cursor' then
                (* OVERFLOWING *)
                Some { pos with cursor= [{ elem with is_overflowing= true }] }
              else
                Option.bind (go_up pos) (go_next_going_up tagDefs)

        end    
    | _ ->
        Cerb_debug.error "TODO: do_next_in_same_level _"


module E = struct
  include Cabs_to_ail_effect
  let return = State_exception.stExpect_return
  let bind = State_exception.stExpect_bind
  let constraint_violation loc v =
    fun _ -> Exception.fail (loc, Errors.DESUGAR (Errors.Desugar_ConstraintViolation v))
  let undef loc ub =
    fun _ -> Exception.fail  (loc, Errors.DESUGAR (Errors.Desugar_UndefinedBehaviour ub))
end
let (>>=) = E.bind

let find_struct_member tagDefs ident tag_sym =
  let (x, xs, flex_opt) = lookup_struct_members tagDefs tag_sym in
  match List.find_index (fun x -> Symbol.equal_identifier (fst x) ident) (x::xs) with
    | Some i ->
        begin match Lem_list.split_at i (x::xs) with
          | (prev, (_, ty) :: next) ->
              Either.Right (ty, prev, next)
          | _ ->
              Cerb_debug.error "Desugaring_init.find_struct_member"
        end
    | None ->
        let is_flexible_array_member =
          match flex_opt with
            | Some (Ctype.FlexibleArrayMember (_, flex_ident, _, _)) ->
                Symbol.equal_identifier ident flex_ident
            | None ->
                false in
        Left is_flexible_array_member

let find_union_member tagDefs ident tag_sym =
  let (x, xs) = lookup_union_members tagDefs tag_sym in
  List.assoc_opt ident (x::xs)


type desugaring_init_funcs = {
  desugar_expression: Cabs.cabs_expression -> (unit AilSyntax.expression) E.desugM;
  is_integer_constant_expression: unit AilSyntax.expression -> bool E.desugM;
  is_initializer_constant_expression_or_string_literal: unit AilSyntax.expression -> bool E.desugM;
  evaluate_integer_constant_expression: Cerb_location.t -> Ctype.ctype option -> unit AilSyntax.expression -> Z.t E.desugM;
}

let liftM = function
  | Some z ->
      E.return z
  | None ->
      Cerb_debug.error "TODO: liftM fail"


let rec go_top_of_block pos =
  match go_up_stop_at_block pos with
    | None ->
        pos
    | Some pos' ->
      go_top_of_block pos'


let rec moveTo_aux tagDefs funcs is_top (ty_acc, cursor_acc) desigs =
  let moveTo_aux = moveTo_aux tagDefs funcs false in
  match desigs with
    | [] ->
        E.return (ty_acc, cursor_acc)
    | Cabs.Desig_array e :: desigs' ->
        let loc = Loc.locOf_cabs_expr e in
        let common e =
          funcs.desugar_expression e               >>= fun d_e ->
          funcs.is_integer_constant_expression d_e >>= function
            | false ->
                E.constraint_violation loc Constraint.IllegalTypeArrayDesignator
            | true ->
              funcs.evaluate_integer_constant_expression loc None d_e >>= fun idx ->
              if Z.(lt idx zero) then
                E.constraint_violation loc Constraint.IllegalSizeArrayDesignator
              else
                E.return idx in
        begin match unatomic ty_acc with
          | Ctype (_, Array (elem_ty, Some size)) ->
              common e >>= fun idx ->
              let new_elem =
                if Z.geq idx size then
                  (* TODO: let* () = Eff.warn "array designator is larger than array" in *)
                  { is_block= is_top; is_overflowing= true; kind= Init_array (Z.pred size, Some size) }
                else
                  { is_block= is_top; is_overflowing= false; kind= Init_array (idx, Some size) } in
              moveTo_aux (elem_ty, new_elem :: cursor_acc) desigs'
          | Ctype (_, Array (elem_ty, None)) ->
              common e >>= fun idx ->
              let new_elem = { is_block= is_top; is_overflowing= false; kind= Init_array (idx, None) } in
              moveTo_aux (elem_ty, new_elem :: cursor_acc) desigs'
          | _ ->
              E.constraint_violation loc Constraint.IllegalArrayDesignatorUsage
        end
    | Cabs.Desig_member ident :: desigs' ->
        let loc = Loc.locOf_identifier ident in
        begin match unatomic ty_acc with
          | Ctype (_, Struct tag_sym) ->
            begin match find_struct_member tagDefs ident tag_sym with
              | Right (new_ty, prev, next) ->
                  let elem' = { is_block= is_top; is_overflowing= false; kind= Init_struct (tag_sym, prev, ident, next) } in
                  moveTo_aux (new_ty, elem' :: cursor_acc) desigs'
              | Left is_flexible_array_member ->
                  if is_flexible_array_member then
                    E.constraint_violation loc (Constraint.IllegalMemberDesignatorFlexibleArrayMember ident)
                  else
                    E.constraint_violation loc (Constraint.IllegalMemberDesignator (ident, ty_acc))
            end
          | Ctype (_, Union tag_sym) ->
              begin match find_union_member tagDefs ident tag_sym with
                | Some new_ty ->
                    let elem' = { is_block= is_top; is_overflowing= false; kind= Init_union (tag_sym, ident) } in
                    moveTo_aux (new_ty, elem' :: cursor_acc) desigs'
                | None ->
                    E.constraint_violation loc (Constraint.IllegalMemberDesignator (ident, ty_acc))
              end
          | _ ->
              E.constraint_violation loc Constraint.IllegalMemberDesignatorUsage
        end

let moveTo tagDefs funcs pos = function
  | None ->
      E.return pos
  | Some desigs ->
      liftM (go_up (go_top_of_block pos))                       >>= fun pos            ->
      moveTo_aux tagDefs funcs true (pos.ty, pos.cursor) desigs >>= fun (ty', cursor') ->
      E.return { pos with ty= ty'; cursor= cursor' }

let rec on_list pos f = function
  | [] ->
      E.return pos
  | [x] ->
      f true pos x
  | x :: xs ->
      f false pos x >>= fun pos' ->
      on_list pos' f xs


type init_element =
  | Elem_array of Z.t
  | Elem_member of Symbol.identifier
  | Elem_union
[@@deriving ord]
type init_path = init_element list
[@@deriving ord]

module InitPathMap = Map.Make(struct
  type t = init_path
  let compare = compare_init_path
end)

type init_map = (unit AilSyntax.expression) InitPathMap.t


let to_init_path cursor =
  let aux elem =
    match elem.kind with
      | Init_array (n, _) ->
          Elem_array n
      | Init_struct (_, _, ident, _) ->
          Elem_member ident
      | Init_union (_, ident) ->
          Elem_union in
  List.map aux (List.rev cursor)

let rec interp_initializer_aux tagDefs funcs is_static_or_thread inits_acc is_inner max_index pos = function
  | Cabs.Init_expr e ->
      funcs.desugar_expression e >>= fun d_e ->
      funcs.is_initializer_constant_expression_or_string_literal d_e >>= begin function
        | false ->
            if is_static_or_thread then
              (* STD §6.7.9#4 *)
              E.constraint_violation (Loc.locOf_ail_expr d_e) Constraint.IllegalStorageClassStaticOrThreadInitializer
            else
              E.return ()
        | true ->
            E.return ()
      end >>= fun () ->
      if false (* is_compound_literal OR string literal *) then
        Cerb_debug.error "TODO: explode the elements"
      else
        (* NOTE: we dealing with a scalar, so we go down to a leaf *)
        let pos = go_bottom tagDefs pos in
        let inits_acc' =
          if cursor_overflowing pos.cursor then
            inits_acc
          else
            InitPathMap.add (to_init_path pos.cursor) d_e inits_acc in
        E.return (max_index, inits_acc', false, pos)
  | Cabs.Init_list (loc, xs) ->
      if AilTypesAux.is_scalar (unatomic pos.ty) then
        match xs with
          | [(None, Cabs.Init_expr e)] ->
              interp_initializer_aux tagDefs funcs is_static_or_thread inits_acc is_inner max_index pos (Cabs.Init_expr e)
          | _ ->
              E.undef loc Undefined.UB081_scalar_initializer_not_single_expression
      else
        (* NOTE: we go on step down (an mark the opening of a block { ... }) *)
        (* NOTE: this moves the cursor to the first member/index of the struct/array *)
        liftM (go_down_entering_block tagDefs pos) >>= fun pos ->
        (* NOTE: for each element of the init list *)
        on_list (max_index, inits_acc, pos) (fun is_last (max_index, inits_acc, pos) (desigs_opt, init) ->
          (* NOTE: we move to the position specified by the designators *)
          moveTo tagDefs funcs pos desigs_opt >>= fun pos' ->
          (* this keeps track of the largest index used when initialising an array with unknown size *)
          let max_index' =
            if is_inner then
              max_index
            else match pos'.cursor with
              | [] -> max_index
              | elem :: _ ->
                  begin match elem.kind with
                    | Init_array (idx, None) ->
                        if Z.gt idx max_index then idx else max_index
                    | _ ->
                        max_index
                  end in
          (* NOTE: we recursively interpret the inner initializer (this may move the cursor) *)
          (* NOTE: the max_index doesn't matter here because we can only have an aray with unknown size at the top-level *)
          interp_initializer_aux tagDefs funcs is_static_or_thread inits_acc true Z.zero pos' init
            >>= fun (_, inits_acc', finished_list, pos') ->
          begin if is_last then
            if not is_inner then
              (* NOTE: the whole initiliazer_ has been interpreted *)
              E.return pos'
            else
              (* NOTE: if we are dealing with the LAST element of the init list *)
              (* NOTE: we move the cursor back to the level of the block we just opened *)
              let pos' = go_top_of_block pos' in
              (* NOTE: we move up from this block *)
              (* TODO: if we were overflowing before entering the block we need to STILL be overflowing *)
              liftM (go_up (unmark_as_overflowing pos')) >>= fun pos' ->
              liftM (do_next_in_same_level tagDefs pos') >>= fun pos' ->
              E.return pos'
          else
            (* NOTE: otherwise (not the last element), we move to the next (logical) position *)
            if cursor_overflowing pos'.cursor then
              (* NOTE: if there is another initialiser in the list,
                we are un excess (we'll ignore, maybe warn) *)
              E.return pos'
            else if finished_list then
              E.return pos'
            else
              liftM (go_next tagDefs pos')
          end >>= fun pos' ->
          (* NOTE: in the union, the bindings of the second map take precedence *)
          E.return (max_index', inits_acc', pos')
        ) xs >>= fun (max_index, inits, pos) ->
        E.return (max_index, inits, true, pos)

let interp_initializer_ tagDefs funcs is_static_or_thread pos xs =
  interp_initializer_aux tagDefs funcs is_static_or_thread InitPathMap.empty false Z.zero pos xs >>= fun (max_index, inits, _, last_pos) ->
  E.return (max_index, inits, last_pos)


let desugar_init tagDefs f1 f2 f3 f4 is_static_or_thread ty init =
  let funcs =
    { desugar_expression= f1
    ; is_integer_constant_expression= f2
    ; is_initializer_constant_expression_or_string_literal= f3
    ; evaluate_integer_constant_expression= f4 } in
  let pos = { block_ty= ty; ty= ty; cursor= []; in_block= false } in
  interp_initializer_ tagDefs funcs is_static_or_thread pos init >>= fun (size, init_map, last_pos) ->
  let ty' =
    match ty with
      | Ctype (annots, Array (elem_ty, None)) ->
          Ctype (annots, Array (elem_ty, Some (Z.succ size)))
      | _ ->
          ty in
  E.return (ty', init_map(*, last_pos*))


let rec constructValue_aux tagDefs path init_map (Ctype.Ctype (_, ty) as cty) =
  let loc = Cerb_location.other "Cabs_to_ail.constructValue" in
  let wrap_expr expr_ = AilSyntax.AnnotatedExpression ((), [], loc, expr_) in
  match ty with
    | Ctype.Array (_, None) ->
        Cerb_debug.error "constructValue_aux: Array None"
    | Ctype.Array (elem_ty, Some n) ->
        let es =
          List.map (fun i ->
            Some (constructValue_aux tagDefs (path @ [Elem_array i]) init_map elem_ty)
          ) (Utils.mkListN n) in
        wrap_expr (AilSyntax.AilEarray (false(*TODO*), elem_ty, es))
    | Ctype.Struct tag_sym ->
        begin match Pmap.lookup tag_sym tagDefs with
          | Some (Struct_definition (_, _, isAnonymous, xs, _)) ->
              let () = if isAnonymous then
                Cerb_debug.print_debug 2 [] (fun () ->
                  "constructValue_aux: this may be WRONG ==> anonymous Struct"
                )
              else () in
              let membrs = List.map (fun (memb_ident, (_, _, _, memb_ty)) ->
                (* TODO: this is only correct if the first member was the one initialised *)
                (memb_ident, Some (constructValue_aux tagDefs (path @ [Elem_member memb_ident]) init_map memb_ty))
              ) xs in
              wrap_expr (AilSyntax.AilEstruct (tag_sym, membrs))
          | _ ->
              Cerb_debug.error "constructValue_aux, Struct"
        end
    | Ctype.Union tag_sym ->
        begin match Pmap.lookup tag_sym tagDefs with
          | Some (Union_definition (_, _, isAnonymous, (first_memb_ident, (_, _, _, first_memb_ty)) :: _)) ->
              let () = if isAnonymous then
                Cerb_debug.print_debug 2 [] (fun () ->
                  "constructValue_aux: this may be WRONG ==> anonymous Union"
                )
              else () in
              let () = Cerb_debug.print_debug 0 [] (fun () ->
                "constructValue_aux: is WRONG for union ==> always assigning the first member"
              ) in
              wrap_expr begin
                AilSyntax.AilEunion (tag_sym, first_memb_ident,
                  Some (constructValue_aux tagDefs (path @ [Elem_union]) init_map first_memb_ty))
              end
          | _ ->
              Cerb_debug.error "constructValue_aux, Union"
        end
    | Ctype.Atomic ty' ->
        (* TODO: check this *)
        constructValue_aux tagDefs path init_map ty'
    | _ ->
        begin match InitPathMap.find_opt path init_map with
          | None ->
              mk_zeroInit tagDefs cty
          | Some e ->
              e
        end

let constructValue tagDefs init_map ty =
  constructValue_aux tagDefs [] init_map ty
