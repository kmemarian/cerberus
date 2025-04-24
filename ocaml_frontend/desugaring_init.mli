open Ctype
open Cabs_to_ail_aux
open Cabs_to_ail_effect

type init_map

val desugar_init:
  (union_tag, tag_definition0) Pmap.map ->
  (Cabs.cabs_expression -> (unit AilSyntax.expression) desugM) ->
  (unit AilSyntax.expression -> bool desugM) ->
  (unit AilSyntax.expression -> bool desugM) ->
  (Cerb_location.t -> ctype option -> unit AilSyntax.expression -> Z.t desugM) ->
  bool ->
  ctype -> Cabs.initializer_ ->
  (Ctype.ctype * init_map) desugM

val constructValue:
  (union_tag, tag_definition0) Pmap.map ->
  init_map ->
  ctype ->
  unit AilSyntax.expression