(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

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
val define : Names.Id.t -> Evd.evar_map -> EConstr.t -> Names.GlobRef.t
