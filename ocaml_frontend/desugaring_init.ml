open import Pervasives Utils Cabs

open import Ctype
open import Cabs_to_ail_aux
import Cabs_to_ail_effect
import AilTypesAux Constraint

type init_cursor_kind =
  | Init_array of integer(* current index*) * maybe integer(* size (nothing if we are dealing with a top-level unknown sized array) *)
  | Init_struct of Symbol.sym * list (Symbol.identifier * ctype) * Symbol.identifier * list (Symbol.identifier * ctype)
  | Init_union of Symbol.sym * Symbol.identifier

type init_cursor_elem = <|
  is_block: bool; (* indicates whether an Init_list was entered *)
  is_overflowing: bool; (* indicates whether the cursor has overflowed (the current struct or array) *)
  kind: init_cursor_kind;
|>

type init_position = <|
  block_ty: ctype; (* type of the current { .. } *)
  ty: ctype; (* type at the cursor *)
  cursor: list init_cursor_elem;
  in_block: bool;
|>

let mark_as_overflowing pos =
  let cursor =
    match pos.cursor with
      | elem :: cursor' ->
          <| elem with is_overflowing= true |> :: cursor'
      | z -> z
    end in
  <| pos with cursor= cursor |>

let unmark_as_overflowing pos =
  let cursor =
    match pos.cursor with
      | elem :: cursor' ->
          <| elem with is_overflowing= false |> :: cursor'
      | z -> z
    end in
  <| pos with cursor= cursor |>

let cursor_overflowing = function
  | [] ->
      false
  | elem :: _ ->
      elem.is_overflowing
end

let lookup_struct_members tagDefs tag_sym =
  let aux (ident, (_, _, _, ty)) = (ident, ty) in
  match Map.lookup tag_sym tagDefs with
    | Just (Struct_definition _ _ _ (x::xs) flex_opt) ->
        (aux x, List.map aux xs, flex_opt)
    | _ ->
        error "Desugaring_init.lookup_struct_members: Nothing or empty Struct definition"
  end

let lookup_union_members tagDefs tag_sym =
  let aux (ident, (_, _, _, ty)) = (ident, ty) in
  match Map.lookup tag_sym tagDefs with
    | Just (Union_definition _ _ _ (x::xs)) ->
        (aux x, List.map aux xs)
    | _ ->
        error "Desugaring_init.lookup_union_members: Nothing or empty Union definition"
  end

val go_down_aux: map Symbol.sym tag_definition -> bool -> init_position -> maybe init_position
let go_down_aux tagDefs entering_block pos =
  if cursor_overflowing pos.cursor then
    (* OVERFLOWING *)
    Nothing
  else
    let mk_cursor_elem kind =
      <| is_block= entering_block; is_overflowing= false; kind= kind |> in
    match unatomic pos.ty with
      | Ctype _ (Basic _) ->
          Nothing
      | Ctype _ (Pointer _ _) ->
          Nothing
      | Ctype _  (Array elem_ty size_opt) ->
          Just <| pos with ty= elem_ty; cursor= mk_cursor_elem (Init_array 0 size_opt) :: pos.cursor |>
      | Ctype _  (Struct tag_sym) ->
          let ((first_ident, first_ty), other_membrs, _) = lookup_struct_members tagDefs tag_sym in
          Just <| pos with ty= first_ty; cursor= mk_cursor_elem (Init_struct tag_sym [] first_ident other_membrs) :: pos.cursor |>
      | Ctype _ (Union tag_sym) ->
          let ((first_ident, first_ty), _) = lookup_union_members tagDefs tag_sym in
          Just <| pos with ty= first_ty; cursor= mk_cursor_elem (Init_union tag_sym first_ident) :: pos.cursor |>
      | _ ->
          let ty_str = Pp.stringFromAil_ctype no_qualifiers pos.ty in
          error ("Desugaring_init.go_down_aux NOT Basic, Array, Struct, Union ==> " ^ ty_str)
    end

let go_down                tagDefs pos = go_down_aux tagDefs false pos
let go_down_entering_block tagDefs pos = go_down_aux tagDefs true  pos

val     go_bottom: map Symbol.sym tag_definition -> init_position -> init_position
let rec go_bottom tagDefs pos =
  match go_down tagDefs pos with
    | Just pos ->
        go_bottom tagDefs pos
    | Nothing ->
        pos
  end


val go_up_aux: bool -> init_position -> maybe init_position
let go_up_aux stop_at_block pos =
  match pos.cursor with
    | [] ->
        Nothing
    | elem :: cursor' ->
        match elem.kind with
          | Init_array _ size_opt ->
              if stop_at_block && elem.is_block then
                Nothing
              else
                Just <| pos with ty= Ctype [] (Array pos.ty size_opt); cursor= cursor'|>
          | Init_struct tag_sym _ _ _ ->
              if stop_at_block && elem.is_block then
                Nothing
              else
                Just <| pos with ty= Ctype [] (Struct tag_sym); cursor= cursor' |>
          | Init_union tag_sym _ ->
              if stop_at_block && elem.is_block then
                Nothing
              else
                Just <| pos with ty= Ctype [] (Union tag_sym); cursor= cursor' |>
        end
  end

let go_up               pos = go_up_aux false pos
let go_up_stop_at_block pos = go_up_aux true  pos


val     go_next_aux: map Symbol.sym tag_definition -> bool -> init_position -> maybe init_position
let rec go_next_aux tagDefs going_up pos =
  if cursor_overflowing pos.cursor then
    (* TODO: check (OVERFLOWING) *)
    Nothing
  else match pos.cursor with
    | [] ->
        go_down tagDefs pos
    | elem :: cursor' ->
        match elem.kind with
          | Init_array current_idx size_opt ->
              let new_idx = current_idx + 1 in
              let index_is_overflowing =
                match size_opt with
                  | Just size -> new_idx >= size
                  | Nothing   -> false
                end in
              if index_is_overflowing then
                if elem.is_block then
                  (* OVERFLOWING *)
                  Just <| pos with cursor= <| elem with is_overflowing= true |> :: cursor' |>
                else
                  Maybe.bind (go_up pos) (go_next_going_up tagDefs)
              else if AilTypesAux.is_scalar (unatomic pos.ty) || going_up then
                Just <| pos with cursor= <| is_block= elem.is_block; is_overflowing= elem.is_overflowing; kind= Init_array new_idx size_opt |> :: cursor' |>
              else
                Maybe.bind (go_down tagDefs pos) (go_next tagDefs)
          | Init_struct _ _ _ [] ->
              if elem.is_block then
                (* OVERFLOWING *)
                Just <| pos with cursor= <| elem with is_overflowing= true |> :: cursor' |>
              else
                Maybe.bind (go_up pos) (go_next_going_up tagDefs)
          | Init_struct tag_sym prev_membrs current_member next_membrs ->
              let (memb_ident, memb_ty) = List_extra.head next_membrs in
              if AilTypesAux.is_scalar (unatomic pos.ty) || going_up then
                Just <| pos with ty= memb_ty; cursor= <| elem with kind=
                  Init_struct tag_sym(prev_membrs ++ [(current_member, pos.ty)]) memb_ident (List_extra.tail next_membrs) |> :: cursor' |>
              else
                Maybe.bind (go_down tagDefs pos) (go_next tagDefs)
          | Init_union _ _ ->
              if elem.is_block then
                (* OVERFLOWING *)
                Just <| pos with cursor= <| elem with is_overflowing= true |> :: cursor' |>
              else
                Maybe.bind (go_up pos) (go_next_going_up tagDefs)
        end
  end

and go_next          tagDefs pos = go_next_aux tagDefs false pos
and go_next_going_up tagDefs pos = go_next_aux tagDefs true  pos


val do_next_in_same_level: map Symbol.sym tag_definition -> init_position -> maybe init_position
let do_next_in_same_level tagDefs pos =
  if cursor_overflowing pos.cursor then
    Just pos
  else match pos.cursor with
    | elem :: cursor' ->
        match elem.kind with
          | Init_array current_idx size_opt ->
              let new_idx = current_idx + 1 in
              let index_is_overflowing =
                match size_opt with
                  | Just size -> new_idx >= size
                  | Nothing   -> false
                end in
              if index_is_overflowing then
                if cursor' = [] then
                  (* OVERFLOWING *)
                  Just <| pos with cursor= <| elem with is_overflowing= true |> :: cursor' |>
                else
                  Maybe.bind (go_up pos) (go_next_going_up tagDefs)
              else
                Just <| pos with cursor= <| elem with kind= Init_array new_idx size_opt |> :: cursor' |>
          | Init_struct _ _ _ [] ->
              if cursor' = [] then
                (* OVERFLOWING *)
                Just <| pos with cursor= [<| elem with is_overflowing= true |>] |>
              else
                Maybe.bind (go_up pos) (go_next_going_up tagDefs)
          | Init_struct tag_sym prev_membrs current_member ((memb_ident, memb_ty) :: next_membrs) ->
              Just (<| pos with ty= memb_ty; cursor= <| elem with kind= Init_struct tag_sym (prev_membrs ++ [(current_member, pos.ty)]) memb_ident next_membrs |> :: cursor' |>)
          | Init_union _ _ ->
              if cursor' = [] then
                (* OVERFLOWING *)
                Just <| pos with cursor= [<| elem with is_overflowing= true |>] |>
              else
                Maybe.bind (go_up pos) (go_next_going_up tagDefs)

        end    
    | _ ->
        error "TODO: do_next_in_same_level _"
  end


module E = Cabs_to_ail_effect
let inline (>>=) = E.bind

let find_struct_member tagDefs ident tag_sym =
  let (x, xs, flex_opt) = lookup_struct_members tagDefs tag_sym in
  match List.findIndex (fun x -> fst x = ident) (x::xs) with
    | Just i ->
        match List.splitAt i (x::xs) with
          | (prev, (_, ty) :: next) ->
              Right (ty, prev, next)
          | _ ->
              error "Desugaring_init.find_struct_member"
        end
    | Nothing ->
        let is_flexible_array_member =
          match flex_opt with
            | Just (Ctype.FlexibleArrayMember _ flex_ident _ _) ->
                ident = flex_ident
            | Nothing ->
                false
          end in
        Left is_flexible_array_member
  end

let find_union_member tagDefs ident tag_sym =
  let (x, xs) = lookup_union_members tagDefs tag_sym in
  List.lookup ident (x::xs)

import AilSyntax

type desugaring_init_funcs = <|
  desugar_expression: Cabs.cabs_expression -> E.desugM (AilSyntax.expression unit);
  is_integer_constant_expression: AilSyntax.expression unit -> E.desugM bool;
  is_initializer_constant_expression_or_string_literal: AilSyntax.expression unit -> E.desugM bool;
  evaluate_integer_constant_expression: Loc.t -> maybe Ctype.ctype -> AilSyntax.expression unit -> E.desugM integer;
|>

let liftM = function
  | Just z ->
      E.return z
  | Nothing ->
      error "TODO: liftM fail"
end


let rec go_top_of_block pos =
  match go_up_stop_at_block pos with
    | Nothing ->
        pos
    | Just pos' ->
      go_top_of_block pos'
  end


let rec moveTo_aux tagDefs funcs is_top (ty_acc, cursor_acc) desigs =
  let moveTo_aux = moveTo_aux tagDefs funcs false in
  match desigs with
    | [] ->
        E.return (ty_acc, cursor_acc)
    | Cabs.Desig_array e :: desigs' ->
        let loc = Loc.locOf e in
        let common e =
          funcs.desugar_expression e               >>= fun d_e ->
          funcs.is_integer_constant_expression d_e >>= function
            | false ->
                E.constraint_violation loc Constraint.IllegalTypeArrayDesignator
            | true ->
              funcs.evaluate_integer_constant_expression loc Nothing d_e >>= fun idx ->
              if idx < 0 then
                E.constraint_violation loc Constraint.IllegalSizeArrayDesignator
              else
                E.return idx
          end in
        match unatomic ty_acc with
          | Ctype _ (Array elem_ty (Just size)) ->
              common e >>= fun idx ->
              let new_elem =
                if idx >= size then
                  (* TODO: let* () = Eff.warn "array designator is larger than array" in *)
                  <| is_block= is_top; is_overflowing= true; kind= Init_array (size-1) (Just size) |>
                else
                  <| is_block= is_top; is_overflowing= false; kind= Init_array idx (Just size) |> in
              moveTo_aux (elem_ty, new_elem :: cursor_acc) desigs'
          | Ctype _ (Array elem_ty Nothing) ->
              common e >>= fun idx ->
              let new_elem = <| is_block= is_top; is_overflowing= false; kind= Init_array idx Nothing |> in
              moveTo_aux (elem_ty, new_elem :: cursor_acc) desigs'
          | _ ->
              E.constraint_violation loc Constraint.IllegalArrayDesignatorUsage
        end
    | Cabs.Desig_member ident :: desigs' ->
        let loc = Loc.locOf ident in
        match unatomic ty_acc with
          | Ctype _ (Struct tag_sym) ->
            match find_struct_member tagDefs ident tag_sym with
              | Right (new_ty, prev, next) ->
                  let elem' = <| is_block= is_top; is_overflowing= false; kind= Init_struct tag_sym prev ident next |> in
                  moveTo_aux (new_ty, elem' :: cursor_acc) desigs'
              | Left is_flexible_array_member ->
                  if is_flexible_array_member then
                    E.constraint_violation loc (Constraint.IllegalMemberDesignatorFlexibleArrayMember ident)
                  else
                    E.constraint_violation loc (Constraint.IllegalMemberDesignator ident ty_acc)
            end
          | Ctype _ (Union tag_sym) ->
              match find_union_member tagDefs ident tag_sym with
                | Just new_ty ->
                    let elem' = <| is_block= is_top; is_overflowing= false; kind= Init_union tag_sym ident |> in
                    moveTo_aux (new_ty, elem' :: cursor_acc) desigs'
                | Nothing ->
                    E.constraint_violation loc (Constraint.IllegalMemberDesignator ident ty_acc)
              end
          | _ ->
              E.constraint_violation loc Constraint.IllegalMemberDesignatorUsage
        end
  end

let moveTo tagDefs funcs pos = function
  | Nothing ->
      E.return pos
  | Just desigs ->
      liftM (go_up (go_top_of_block pos))                       >>= fun pos            ->
      moveTo_aux tagDefs funcs true (pos.ty, pos.cursor) desigs >>= fun (ty', cursor') ->
      E.return <| pos with ty= ty'; cursor= cursor' |>
end

val     on_list: forall 'a 'b. 'a -> (bool -> 'a -> 'b -> E.desugM 'a) -> list 'b -> E.desugM 'a
let rec on_list pos f = function
  | [] ->
      E.return  pos
  | [x] ->
      f true pos x
  | x :: xs ->
      f false pos x >>= fun pos' ->
      on_list pos' f xs
end


type init_element =
  | Elem_array of integer
  | Elem_member of Symbol.identifier
  | Elem_union
type init_path = list init_element

let stringFromInit_element = function
  | Elem_array n ->
      "[" ^ show n ^ "]"
  | Elem_member ident ->
      "." ^ show ident
  | Elem_union ->
      ".UNION"
end


instance (SetType init_element)
  let setElemCompare elem1 elem2 =
    let ord = function
      | Elem_array _ ->
          (0 : nat)
      | Elem_member _ ->
          1
      | Elem_union ->
          2
    end in
    match (elem1, elem2) with
      | (Elem_array n1, Elem_array n2) ->
          setElemCompare n1 n2
      | (Elem_member ident1, Elem_member ident2) ->
          setElemCompare ident1 ident2
      | _ ->
          setElemCompare (ord elem1) (ord elem2)
    end
end


let stringFromInit_path xs =
  String.concat "" (List.map stringFromInit_element xs)


val to_init_path: list init_cursor_elem -> init_path
let to_init_path cursor =
  let aux elem =
    match elem.kind with
      | Init_array n _ ->
          Elem_array n
      | Init_struct _ _ ident _ ->
          Elem_member ident
      | Init_union _ ident ->
          Elem_union
    end in
  List.map aux (List.reverse cursor)

let rec interp_initializer_aux tagDefs funcs is_static_or_thread inits_acc is_inner max_index pos = function
  | Cabs.Init_expr e ->
      funcs.desugar_expression e >>= fun d_e ->
      funcs.is_initializer_constant_expression_or_string_literal d_e >>= function
        | false ->
            if is_static_or_thread then
              (* STD §6.7.9#4 *)
              E.constraint_violation (Loc.locOf d_e) Constraint.IllegalStorageClassStaticOrThreadInitializer
            else
              E.return ()
        | true ->
            E.return ()
      end >>= fun () ->
      if false (* is_compound_literal OR string literal *) then
        error "TODO: explode the elements"
      else
        (* NOTE: we dealing with a scalar, so we go down to a leaf *)
        let pos = go_bottom tagDefs pos in
        let inits_acc' =
          if cursor_overflowing pos.cursor then
            inits_acc
          else
            Map.insert (to_init_path pos.cursor) d_e inits_acc in
        E.return (max_index, inits_acc', false, pos)
  | Cabs.Init_list loc xs ->
      if AilTypesAux.is_scalar (unatomic pos.ty) then
        match xs with
          | [(Nothing, Cabs.Init_expr e)] ->
              interp_initializer_aux tagDefs funcs is_static_or_thread inits_acc is_inner max_index pos (Cabs.Init_expr e)
          | _ ->
              E.undef loc Undefined.UB081_scalar_initializer_not_single_expression
        end
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
                  match elem.kind with
                    | Init_array idx Nothing ->
                        if idx > max_index then idx else max_index
                    | _ ->
                        max_index
                  end
            end in
          (* NOTE: we recursively interpret the inner initializer (this may move the cursor) *)
          (* NOTE: the max_index doesn't matter here because we can only have an aray with unknown size at the top-level *)
          interp_initializer_aux tagDefs funcs is_static_or_thread inits_acc true 0 pos' init
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
end

let interp_initializer_ tagDefs funcs is_static_or_thread pos xs =
  interp_initializer_aux tagDefs funcs is_static_or_thread Map.empty false 0 pos xs >>= fun (max_index, inits, _, last_pos) ->
  E.return (max_index, inits, last_pos)


let desugar_init tagDefs funcs is_static_or_thread ty init =
  let pos = <| block_ty= ty; ty= ty; cursor= []; in_block= false |> in
  interp_initializer_ tagDefs funcs is_static_or_thread pos init >>= fun (size, init_map, last_pos) ->
  let ty' =
    match ty with
      | Ctype annots (Array elem_ty Nothing) ->
          Ctype annots (Array elem_ty (Just (size + 1)))
      | _ ->
          ty
    end in
  E.return (ty', init_map, last_pos)


val constructValue: map Symbol.sym tag_definition -> map init_path (AilSyntax.expression unit) -> Ctype.ctype -> AilSyntax.expression unit
let rec constructValue_aux tagDefs path init_map (Ctype.Ctype _ ty as cty) =
  let loc = Loc.other "Cabs_to_ail.constructValue" in
  let wrap_expr expr_ = AilSyntax.AnnotatedExpression () [] loc expr_ in
  match ty with
    | Ctype.Array _ Nothing ->
        error "constructValue_aux: Array Nothing"
    | Ctype.Array elem_ty (Just n) ->
        let es =
          List.map (fun i ->
            Just (constructValue_aux tagDefs (path ++ [Elem_array i]) init_map elem_ty)
          ) (Utils.mkListN n) in
        wrap_expr (AilSyntax.AilEarray false(*TODO*) elem_ty es)
    | Ctype.Struct tag_sym ->
        match Map.lookup tag_sym tagDefs with
          | Just (Struct_definition _ _ isAnonymous xs _) ->
              let () = if isAnonymous then
                Debug.print_debug 2 [] (fun () ->
                  "constructValue_aux: this may be WRONG ==> anonymous Struct"
                )
              else () in
              let membrs = List.map (fun (memb_ident, (_, _, _, memb_ty)) ->
                (* TODO: this is only correct if the first member was the one initialised *)
                (memb_ident, Just (constructValue_aux tagDefs (path ++ [Elem_member memb_ident]) init_map memb_ty))
              ) xs in
              wrap_expr (AilSyntax.AilEstruct tag_sym membrs)
          | _ ->
              error "constructValue_aux, Struct"
        end
    | Ctype.Union tag_sym ->
        match Map.lookup tag_sym tagDefs with
          | Just (Union_definition _ _ isAnonymous ((first_memb_ident, (_, _, _, first_memb_ty)) :: _)) ->
              let () = if isAnonymous then
                Debug.print_debug 2 [] (fun () ->
                  "constructValue_aux: this may be WRONG ==> anonymous Union"
                )
              else () in
              let () = Debug.print_debug 0 [] (fun () ->
                "constructValue_aux: is WRONG for union ==> always assigning the first member"
              ) in
              wrap_expr begin
                AilSyntax.AilEunion tag_sym first_memb_ident
                  (Just (constructValue_aux tagDefs (path ++ [Elem_union]) init_map first_memb_ty))
              end
          | _ ->
              error "constructValue_aux, Union"
        end
    | Ctype.Atomic ty' ->
        (* TODO: check this *)
        constructValue_aux tagDefs path init_map ty'
    | _ ->
        match Map.lookup path init_map with
          | Nothing ->
              mk_zeroInit tagDefs cty
          | Just e ->
              e
        end
  end

let constructValue tagDefs init_map ty =
  constructValue_aux tagDefs [] init_map ty
