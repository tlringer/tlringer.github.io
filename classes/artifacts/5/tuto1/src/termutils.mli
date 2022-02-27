(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

(* TODO make all of these with sigma last, use state monad *)

(* TODO explain *)
val global_state :
  unit ->
  Evd.evar_map * Environ.env
  
(* TODO explain *)
val internalize :
  Environ.env ->
  Evd.evar_map ->
  Constrexpr.constr_expr ->
  Evd.evar_map * EConstr.t

(* TODO explain *)
val print :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  Pp.t

(* TODO explain *)
val define :
  Names.Id.t ->
  Evd.evar_map ->
  EConstr.t ->
  Names.GlobRef.t

(* TODO explain *)
val type_check :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  Evd.evar_map * EConstr.t

(* TODO explain *)
val equal :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  EConstr.t ->
  Evd.evar_map option

(* TODO explain *)
val lookup_definition :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  Evd.evar_map * EConstr.t

(* TODO explain *)
val push_local :
  Names.Name.t Context.binder_annot * EConstr.constr ->
  Environ.env ->
  Environ.env

(* TODO explain, delete if unused *)
val shift :
  EConstr.constr ->
  EConstr.constr

(* TODO explain, delete if unused *)
val fold_args :
  ('b -> 'a -> Evd.evar_map -> Evd.evar_map * 'b) ->
  'b ->
  'a array ->
  Evd.evar_map ->
  Evd.evar_map * 'b
  
