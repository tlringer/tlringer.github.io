(* TODO explain, rename to make it the right thing, fix the name elsewhere including in comments at top level. also note limitations (constants, reduction), make bonus problems *)

let rec arity trm sigma =
  match EConstr.kind sigma trm with
  | Constr.Lambda (n, t, b) ->
     let sigma_b, arity_b = arity b sigma in
     sigma_b, 1 + arity_b
  | Constr.Prod (n, t, b) ->
     let sigma_b, arity_b = arity b sigma in
     sigma_b, 1 + arity_b
  | _ ->
     sigma, 0

(* TODO call in caller, explain, move first, etc etc, mention limitations, etc etc *)
let rec nargs trm sigma =
  match EConstr.kind sigma trm with
  | Constr.App (f, args) ->
     let (sigma_f, nargs_f) = nargs f sigma in
     sigma_f, nargs_f + Array.length args  
  | _ ->
     sigma, 0
     
    
(* TODO call in caller etc etc, extend w/ more of AST or say OK to ignore other AST parts *)
let rec count_in_body env trm1 trm2 sigma =
  let sigma_opt = Termutils.equal env trm1 trm2 sigma in
  if Option.has_some sigma_opt then
    Option.get sigma_opt, 1
  else
    match EConstr.kind sigma trm2 with
    | Constr.Lambda (n, t, b) ->
       let env_b = Termutils.push_local (n, t) env in
       count_in_body env_b trm1 b sigma
    | Constr.Prod (n, t, b) ->
       let env_b = Termutils.push_local (n, t) env in
       count_in_body env_b trm1 b sigma
    | Constr.App (f, args) ->
       let sigma_f, occs_f = count_in_body env trm1 f sigma in
       Termutils.fold_args
         (fun occs arg sigma ->
           let sigma, occs_arg = count_in_body env trm1 arg sigma in
           sigma, occs_arg + occs)
         occs_f
         args
         sigma_f
    | _ ->
       sigma, 0

(* TODO move etc, same caveats as above *)
let rec sub_in env (trm1, trm2) trm3 sigma =
  let sigma_opt = Termutils.equal env trm1 trm3 sigma in
  if Option.has_some sigma_opt then
    Option.get sigma_opt, trm2
  else
    match EConstr.kind sigma trm3 with
    | Constr.Lambda (n, t, b) ->
       let env_b = Termutils.push_local (n, t) env in
       let sigma_t, subbed_t = sub_in env (trm1, trm2) t sigma in
       let sigma_b, subbed_b = sub_in env_b (trm1, trm2) b sigma_t in
       sigma_b, EConstr.mkLambda (n, subbed_t, subbed_b)
    | Constr.Prod (n, t, b) ->
       let env_b = Termutils.push_local (n, t) env in
       let sigma_t, subbed_t = sub_in env (trm1, trm2) t sigma in
       let sigma_b, subbed_b = sub_in env_b (trm1, trm2) b sigma_t in
       sigma_b, EConstr.mkProd (n, subbed_t, subbed_b)
    | Constr.App (f, args) ->
       let sigma_f, subbed_f = sub_in env (trm1, trm2) f sigma in
       let sigma_args, subbed_args =
         Termutils.map_args
           (sub_in env (trm1, trm2))
           args
           sigma_f
       in sigma_args, EConstr.mkApp (subbed_f, subbed_args)
    | _ ->
       sigma, trm3
