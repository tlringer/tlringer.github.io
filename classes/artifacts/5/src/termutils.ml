(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

open Evd

(* --- State monad --- *)

(*
 * All terms in Coq have to carry around evar_maps (found in the Evd module),
 * which store a bunch of constraints about terms that help with things like
 * unification, type inference, and equality checking. This is annoying to
 * deal with, so I usually define some helper functions to make it easier.
 *
 * These come from https://github.com/uwplse/coq-plugin-lib in stateutils.ml,
 * and the idea to use this design pattern comes from my grad school advisor
 * Dan Grossman.
 *
 * For any type 'a, a 'a state is a tuple of an evar_map and a 'a.
 * So basically, a 'a that carries around an evar_map.
 *)
type 'a state = evar_map * 'a

(*
 * These are monadic return and bind. Basically, they let you kind of pretend
 * you're not in the state monad (that is, pretend you're not carrying around
 * an evar_map with you everywhere). If you've ever used Haskell, it's common
 * to have syntax that makes this kind of thing look even nicer.
 *)
let ret a = fun sigma -> sigma, a
let bind f1 f2 = (fun sigma -> let sigma, a = f1 sigma in f2 a sigma)

(* Like List.fold_left, but threading state *)
let fold_left_state f b l sigma =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l

(* List List.map, but threading state *)
let map_state f args =
  bind
    (fold_left_state
       (fun bs a sigma ->
         let sigma, b = f a sigma in
         sigma, b :: bs)
       []
       args)
    (fun fargs -> ret (List.rev fargs))

(* Like fold_left_state, but over arrays *)
let fold_left_state_array f b args =
  fold_left_state f b (Array.to_list args)

(* Like map_state, but over arrays *)
let map_state_array f args =
  bind
    (map_state f (Array.to_list args))
    (fun fargs -> ret (Array.of_list fargs))

(* --- Environments --- *)

(*
 * Environments in the Coq kernel map names to types. Here are a few
 * utility functions for environments.
 *)
               
(*
 * This gets the global environment and the corresponding state:
 *)
let global_env () =
  let env = Global.env () in
  Evd.from_env env, env

(* TODO explain *)
let print env trm sigma =
  Printer.pr_econstr_env env sigma trm

(* TODO explain *)
let internalize env trm sigma =
  Constrintern.interp_constr_evars env sigma trm

(* TODO explain, note highly simplified *)
let define name body sigma =
  let udecl = UState.default_univ_decl in
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~scope ~kind  ~udecl ~poly:false () in
  ignore (Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma)

(* TODO explain *)
let equal env trm1 trm2 sigma =
  Reductionops.infer_conv env sigma trm1 trm2

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env
