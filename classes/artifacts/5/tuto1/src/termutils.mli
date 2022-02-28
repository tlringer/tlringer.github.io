(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

(* TODO make all of these with sigma last, use state monad *)

type 'a state = Evd.evar_map * 'a

(* TODO explain *)
val global_state : unit -> Environ.env state
  
(* TODO explain *)
val internalize :
  Environ.env ->
  Constrexpr.constr_expr ->
  Evd.evar_map ->
  EConstr.t state

(* TODO explain *)
val print :
  Environ.env ->
  EConstr.t ->
  Evd.evar_map ->
  Pp.t

(* TODO explain *)
val define :
  Names.Id.t ->
  EConstr.t ->
  Evd.evar_map ->
  unit

(* TODO explain *)
val equal :
  Environ.env ->
  EConstr.t ->
  EConstr.t ->
  Evd.evar_map ->
  Evd.evar_map option

(* TODO explain *)
val push_local :
  Names.Name.t Context.binder_annot * EConstr.constr ->
  Environ.env ->
  Environ.env

(* TODO explain *)
val fold_left_state :
  ('b -> 'a -> Evd.evar_map -> 'b state) ->
  'b ->
  'a list ->
  Evd.evar_map ->
  'b state

(* TODO explain, etc *)
val map_state :
  ('a -> Evd.evar_map -> 'b state) ->
  'a list ->
  Evd.evar_map ->
  ('b list) state
  
(* TODO explain, delete if unused *)
val fold_args :
  ('b -> 'a -> Evd.evar_map -> 'b state) ->
  'b ->
  'a array ->
  Evd.evar_map ->
  'b state

(* TODO explain, delete if unused *)
val map_args :
  ('a -> Evd.evar_map ->'b state) ->
  'a array ->
  Evd.evar_map ->
  ('b array) state
