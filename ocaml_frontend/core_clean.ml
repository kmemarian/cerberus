module Cerb_internal = struct
  include Cerb_symbol
  module Loc = Cerb_location
  module Mem = Impl_mem
end

open Cerb_internal
open Ctype

(* type binop =
 | OpAdd
 | OpSub
 | OpMul
 | OpDiv
 | OpRem_t
 | OpRem_f
 | OpExp
 | OpEq
 | OpGt
 | OpLt
 | OpGe
 | OpLe
 | OpAnd
 | OpOr *)

type iop =
 | IOpAdd
 | IOpSub
 | IOpMul
 | IOpShl
 | IOpShr
 | IOpDiv
 | IOpRem_t

(* TODO *)
type core_base_type

(* C object values *)
type object_value =
  | OVinteger of Mem.integer_value (* integer value *)
  | OVfloating of Mem.floating_value (* floating-point value *)
  | OVpointer of Mem.pointer_value (* pointer value *)
  | OVarray of loaded_value list (* C array value *)
  | OVstruct of Sym.t * (Identifier.t * Ctype.ctype * Mem.mem_value) list (* C struct value *)
  | OVunion of Sym.t * Identifier.t * Mem.mem_value (* C union value *)

(* potentially unspecified C object values *)
and loaded_value =
  | LVspecified of object_value (* non-unspecified loaded value *)
  | LVunspecified of Ctype.ctype (* unspecified loaded value *)


(* Core values *)
type value =
  | Bobject of object_value (* C object value *)
  | Bloaded of loaded_value (* loaded C object value *)
  | Bunit
  | Btrue
  | Bfalse
  | Bctype of Ctype.ctype (* C type as value *)
  | Blist of core_base_type * value list
  | Btuple of value list (* tuple *)


(* data constructors *)
type ctor =
  | Cnil of core_base_type (* empty list (annotated with the type of the items) *)
  | Ccons (* list cons *)
  | Ctuple (* tuple *)
  | Carray (* C array *)
  | Civmax (* max integer value *)
  | Civmin (* min integer value *)
  | Civsizeof (* sizeof value *)
  | Civalignof (* alignof value *)
  | CivCOMPL (* bitwise complement *)
  | CivAND (* bitwise AND *)
  | CivOR (* bitwise OR *)
  | CivXOR (* bitwise XOR *)
  | Cspecified (* non-unspecified loaded value *)
  | Cunspecified (* unspecified loaded value *)
  | Cfvfromint (* cast integer to floating value *)
  | Civfromfloat (* cast floating to integer value *)
  | CivNULLcap of bool (* CHERI: null capability *)

(* data destructors *)
type dtor =
  | Dnil of core_base_type (* empty list (annotated with the type of the items) *)
  | Dcons (* list cons *)
  | Dtuple (* tuple *)
  | Dspecified (* non-unspecified loaded value *)
  | Dunspecified (* unspecified loaded value *)


type pattern_desc =
  | CaseBase of (Sym.t option * core_base_type)
  | CaseDtor of dtor * pattern list

and pattern = {
  annots: Annot.annot list;
  desc: pattern_desc;
}

type name (* TODO *)

(* type pure_op =
  | Parray_shift of Ctype.ctype
  | Pmember_shift of Sym.t * Identifier.t *)

module Operator = struct
  type nullary =
    | Sizeof of ctype (* TODO: PARAM IN STD *)
    | Alignof of ctype (* TODO: PARAM IN STD *)
    | NULLcap of bool(*is_signed*) (* CHERI: null capability *)

  type unary =
    | Not (* boolean -> boolean *)
    | Ivmin (* of ctype *) (* ctype -> integer *) (* TODO: PARAM IN STD *)
    | Ivmax (* of ctype *) (* ctype -> integer *) (* TODO: PARAM IN STD *)
    | IvCOMPL of integerType (* integer -> integer -> integer *)
    | Conv_int of integerType (* integer -> integer -> integer *)
    | Memberof of Sym.t * Identifier.t (* C struct/union member access *)
    | Member_shift of Sym.t * Identifier.t
    | Cfunction
    | Is_unsigned
    | Bmc_assume
      (* CHERI *)
    | Ptr_tIntValue (* integer -> integer *)
      (* Bytes *)
    | ByteFromInt (* integer -> byte *)
    | IntFromByte (* byte -> integer *)


  type binary =
    | Add | Sub
    | Mul | Div
    | Rem_t | Rem_f
    | Exp
    | Eq
    | Gt | Lt | Ge | Le
    | And | Or
    | WrapI of integerType * iop
    | Catch_exceptional_condition of integerType * iop

    | IvAND of integerType (* bitwise AND *)
    | IvOR of integerType (* bitwise OR *)
    | IvXOR of integerType (* bitwise XOR *)

    | Array_shift of Ctype.ctype
    | Are_compatible

    (* CHERI *)
    | DeriveCap (* (integer, integer) -> integer *)
    | CapAssignValue (* (integer, integer) -> integer *)

  type nary =
    | Tuple | Array
end

(*
TODO:
op/1
  | Cspecified (* non-unspecified loaded value *)
  | Cfvfromint (* cast integer to floating value *)
  | Civfromfloat (* cast floating to integer value *)
op/2
  | Ccons (* list cons *)
*)

type 'pexpr pexpr_desc =  (* Core pure expressions *)
  | PEsym of Sym.t
  | PEimpl of Implementation.implementation_constant
  | PEbase of value
  | PEundef of Loc.t * Undefined.undefined_behaviour
  | PEerror of string * 'pexpr
  | PEnullary of Operator.nullary
  | PEunary of Operator.unary * 'pexpr
  | PEbinary of Operator.binary * 'pexpr * 'pexpr
  | PEnary of Operator.nary * 'pexpr list
  | PElet of pattern * 'pexpr * 'pexpr
  | PEif of 'pexpr * 'pexpr * 'pexpr
  | PEmatch of 'pexpr * (pattern * 'pexpr) list
  | PEcall of name * 'pexpr list
  | PEstruct of Sym.t * (Identifier.t * 'pexpr) list
  | PEunion of Sym.t * Identifier.t * 'pexpr

type pexpr = {
  loc: Loc.t;
  bTy_opt: core_base_type option;
  desc: pexpr pexpr_desc;
}

module Pexpr = struct
  let mk ?(loc=Loc.unknown) ?bTy_opt desc =
    { loc; bTy_opt; desc }

    let sym_ ?loc ?bTy_opt sym = mk ?loc ?bTy_opt (PEsym sym)
    let undef ?bTy_opt ~loc ub = mk ~loc ?bTy_opt (PEundef (loc, ub))
    let add ?loc ?bTy_opt pe1 pe2 = mk ?loc ?bTy_opt (PEbinary (Add, pe1, pe2))
    let sub ?loc ?bTy_opt pe1 pe2 = mk ?loc ?bTy_opt (PEbinary (Sub, pe1, pe2))
    let mul ?loc ?bTy_opt pe1 pe2 = mk ?loc ?bTy_opt (PEbinary (Mul, pe1, pe2))
    let div ?loc ?bTy_opt pe1 pe2 = mk ?loc ?bTy_opt (PEbinary (Div, pe1, pe2))
end

let test pe1 (sym: Sym.t) =
  Pexpr.(add pe1 (sym_ sym))

let test2 pexpr =
  match pexpr.desc with
  | PEbinary (Add, pe1, pe2) ->
      ()
  | _ ->
      ()


let rec iter_pexpr f pexpr =
  f pexpr.desc;
  match pexpr.desc with
  | PEsym _
  | PEimpl _
  | PEbase _
  | PEundef _
  | PEnullary _ ->
      ()
  | PEerror (_, pe)
  | PEunary (_, pe)
  | PEunion (_, _, pe) ->
      iter_pexpr f pe
  | PEbinary (_, pe1, pe2)
  | PElet (_, pe1, pe2) ->
      iter_pexpr f pe1;
      iter_pexpr f pe2
  | PEif (pe1, pe2, pe3) ->
      iter_pexpr f pe1;
      iter_pexpr f pe2;
      iter_pexpr f pe3
  | PEnary (_, pes)
  | PEcall (_, pes) ->
      List.iter (iter_pexpr f) pes
  | PEmatch (pe, xs) ->
      iter_pexpr f pe;
      List.iter (fun (_, pe) -> iter_pexpr f pe) xs
  | PEstruct (_, xs) ->
      List.iter (fun (_, pe) -> iter_pexpr f pe) xs

(* let rec map_pexpr f pexpr =
  f ~loc:pexpr.loc ~bTy_opt:pexpr.bTy_opt @@
  match pexpr.desc with
  | PEsym _ | PEimpl _ | PEbase _ | PEundef _ | PEnullary _ ->
      pexpr.desc
  | PEerror (str, pe) ->
      PEerror (str, map_pexpr f pe)
  | PEunary (uop, pe) ->
      PEunary (uop, map_pexpr f pe)
  | PEunion (tag_sym, membr_ident, pe) ->
      PEunion (tag_sym, membr_ident, map_pexpr f pe)
  | PEbinary (bop, pe1, pe2) ->
      PEbinary (bop, map_pexpr f pe1, map_pexpr f pe2)
  | PElet (pat, pe1, pe2) ->
      PElet (pat, map_pexpr f pe1, map_pexpr f pe2)
  | PEif (pe1, pe2, pe3) ->
      PEif (map_pexpr f pe1, map_pexpr f pe2, map_pexpr f pe3)
  | PEnary (op, pes) ->
      PEnary (op, List.map (map_pexpr f) pes)
  | PEcall (nm, pes) ->
      PEcall (nm, List.map (map_pexpr f) pes)
  | PEmatch (pe, xs) ->
      PEmatch (map_pexpr f pe, List.map (Pair.map_snd (map_pexpr f)) xs)
  | PEstruct (tag_sym, xs) ->
      PEstruct (tag_sym, List.map (Pair.map_snd (map_pexpr f)) xs) *)


(* let subst sym cval =
  let f ~loc ~bTy_opt desc =
    { loc
    ; bTy_opt
    ; desc= match desc with
      | PEsym sym' as desc -> if Sym.equal sym sym' then cval else desc
      | _ -> failwith "TODO"
      } in
  map_pexpr f *)




(* 
action/0
  | Fence of Atomics.memory_order
  | LinuxFence of Linux.linux_memory_order
action/1
  | Kill of kill_kind * pexpr
action/2
  | Create of pexpr * pexpr * Symbol.prefix
  | Alloc of pexpr * pexpr * Symbol.prefix
  | Load of pexpr * pexpr * Atomics.memory_order
  | LinuxLoad of pexpr * pexpr * Linux.linux_memory_order
action/3
  | CreateReadOnly of pexpr * pexpr * pexpr * Symbol.prefix
  | Store of bool * pexpr * pexpr * pexpr * Atomics.memory_order
  | LinuxStore of pexpr * pexpr * pexpr * Linux.linux_memory_order
  | SeqRMW of bool * pexpr * pexpr * Sym.t * pexpr
  | LinuxRMW of pexpr * pexpr * pexpr * Linux.linux_memory_order
action/4
  | RMW of pexpr * pexpr * pexpr * pexpr * Atomics.memory_order * Atomics.memory_order
  | CompareExchangeStrong of pexpr * pexpr * pexpr * pexpr * Atomics.memory_order * Atomics.memory_order
  | CompareExchangeWeak of pexpr * pexpr * pexpr * pexpr * Atomics.memory_order * Atomics.memory_order
 *)

(*
memop/1
  | IntFromPtr of ctype * ctype (* (ctype, ctype, address) -> eff integer *) (* first type is that of the referenced type, second on is type of integer *)
  | PtrFromInt of ctype * ctype (* (ctype, ctype, integer) -> eff address *) (* first type is that of integer, second on is type of reference *)
  | PtrValidForDeref of ctype (* (ctype, address) -> eff boolean *)
  | PtrWellAligned of ctype (* (ctype, address) -> eff boolean *)
  | PtrMemberShift of Sym.t * Identifier.t (* address -> eff address *)
memop/2
  | PtrEq
  | PtrNe
  | PtrLt
  | PtrGt
  | PtrLe
  | PtrGe
  | Ptrdiff (* (address, address) -> eff integer *)
  | PtrArrayShift of ctype (* address -> ctype -> integer -> eff address *)
  | Copy_alloc_id (* (integer, pointer) -> eff pointer *)

memop/3
  | Memcpy
  | Memcmp
  | Realloc

memop/TODO
  | Va_start
  | Va_copy
  | Va_arg
  | Va_end
  | CHERI_intrinsic of string * (Ctype.ctype * list Ctype.ctype)

*)

type kill_kind (* TODO *)

module Test = struct
  type nullary
  type unary
  type binary
  type ternary
  type quaternary

  type memory_order =
    | Atomics_order of Atomics.memory_order
    | Linux_order of Linux.linux_memory_order

  type _ op =
    | Create : prefix -> binary op
    | CreateReadOnly : prefix -> ternary op
    | Alloc : prefix -> binary op
    | Kill : kill_kind -> unary op
    | Store : bool * Atomics.memory_order -> ternary op (* TODO: move ctype out? *)
    | LinuxStore : Linux.linux_memory_order -> ternary op
    | Load : memory_order -> binary op (* TODO: move ctype out? *)
    | SeqRMW : bool -> ternary op
    | RMW : Atomics.memory_order * Atomics.memory_order -> quaternary op
    | Fence : memory_order -> nullary op
    | CompareExchangeStrong : Atomics.memory_order * Atomics.memory_order -> quaternary op
    | CompareExchangeWeak : Atomics.memory_order * Atomics.memory_order -> quaternary op
    | LinuxRMW : Linux.linux_memory_order -> ternary op

  type 'expr oper =
    | Nullary of nullary op
    | Unary of unary op * 'expr
    | Binary of binary op * 'expr * 'expr
end

type pass_by_value_or_pointer = 
  | By_pointer
  | By_value


type polarity = Pos | Neg

type 'expr action = 'expr Test.oper

(* effectful expression *)
type 'expr expr_desc =
  | Epure of pexpr
  | Ememop of Sym.t Mem_common.generic_memop * pexpr list (* pointer op involving memory *)
  | Eaction of polarity * 'expr action (* memory action *)
  | Ematch of pexpr * (pattern * 'expr) list (* pattern matching *)
  | Elet of pattern * pexpr * 'expr
  | Eif of { ctrl: pexpr; then_: 'expr; else_: 'expr }
  | Eccall of pexpr * pexpr * pexpr list (* C function call *)
  | Eproc of name * pexpr list (* Core procedure call *)
  | Eunseq of 'expr list (* unsequenced expressions *)
  | Ewseq of pattern * 'expr * 'expr (* weak sequencing *)
  | Esseq of pattern * 'expr * 'expr (* strong sequencing *)
  | Ebound of 'expr (* $\ldots$and boundary *)
  | End of 'expr list (* nondeterministic sequencing *)
  | Esave of (Sym.t * core_base_type) * (Sym.t * ((core_base_type * (Ctype.ctype * pass_by_value_or_pointer) option) * pexpr)) list * 'expr (* save label *)
  | Erun of Sym.t * pexpr list (* run from label *)
  | Epar of 'expr list (* cppmem-like thread creation *)
(* 
  | Ewait of Mem_common.thread_id (* wait for thread termination *)
  | Eannot of list dyn_annotation * generic_expr 'a Sym.t
  | Eexcluded of nat * generic_action 'a Sym.t
 *)

type expr = {
  loc: Loc.t;
  annots: Annot.annot list;
  desc: expr expr_desc
}



let mk ?(loc=Loc.unknown) ?(annots=[]) desc =
  { loc; annots; desc }


let pure ?loc ?annots pe = mk ?loc ?annots (Epure pe)

let create ?loc ?annots ?(pol=Pos) pref pe1 pe2 =
  mk ?loc ?annots (Eaction (pol, Test.(Binary (Create pref, pe1, pe2))))



(* let ( .@{} ) xs idx = failwith "TODO" *)