(* TODO explain *)

val arity :
  EConstr.t ->
  Evd.evar_map ->
  Evd.evar_map * int

(* TODO something *)
val nargs :
  EConstr.t ->
  Evd.evar_map ->
  Evd.evar_map * int
  
(* TODO move elsewhere *)
val count_in_body :
  Environ.env ->
  EConstr.t ->
  EConstr.t ->
  Evd.evar_map ->
  Evd.evar_map * int

(* TODO move elsewhere etc *)
val sub_in :
  Environ.env ->
  (EConstr.t * EConstr.t) ->
  EConstr.t ->
  Evd.evar_map ->
  Evd.evar_map * EConstr.t
