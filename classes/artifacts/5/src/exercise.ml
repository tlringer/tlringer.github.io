open EConstr
open Termutils

(*
 * Count the number of occurrences of terms equal to src in trm.
 * Make some simplifying assumptions about the format of trm
 * (no pattern matching, no fixpoints, no lets, and so on).
 *
 * I have done this one for you, to help you figure out how to implement sub.
 *)
let rec count env src trm sigma =
  let sigma, is_eq = Termutils.equal env src trm sigma in
  if is_eq then
    sigma, 1
  else
    match kind sigma trm with
    | Constr.Lambda (n, t, b) | Constr.Prod (n, t, b) ->
       let sigma, count_t = count env src t sigma in
       let sigma, count_b = count (push_local (n, t) env) src b sigma in
       sigma, count_t + count_b
    | Constr.App (f, args) ->
       let sigma_f, occs_f = count env src f sigma in
       Termutils.fold_left_state_array
         (fun occs arg sigma ->
           let sigma, occs_arg = count env src arg sigma in
           sigma, occs_arg + occs)
         occs_f
         args
         sigma_f
    | _ ->
       sigma, 0

(*
 * Substitute all occurrences of terms equal to src in trm with dst.
 * Make some simplifying assumptions about the format of trm
 * (no pattern matching, no fixpoints, not lets, and so on).
 *)
let rec sub env (src, dst) trm sigma =
  let sigma, is_eq = Termutils.equal env src trm sigma in
  if is_eq then
    sigma, dst
  else
    match EConstr.kind sigma trm with
    | Constr.Lambda (n, t, b) | Constr.Prod (n, t, b) ->
       let sigma, sub_t = sub env (src, dst) t sigma in
       let sigma, sub_b = sub (push_local (n, t) env) (src, dst) b sigma in
       sigma, EConstr.mkLambda (n, sub_t, sub_b)
    | Constr.App (f, args) ->
       let sigma_f, subbed_f = sub env (src, dst) f sigma in
       let sigma_args, subbed_args =
         Termutils.map_state_array
           (sub env (src, dst))
           args
           sigma_f
       in sigma_args, EConstr.mkApp (subbed_f, subbed_args)
    | _ ->
       sigma, trm
