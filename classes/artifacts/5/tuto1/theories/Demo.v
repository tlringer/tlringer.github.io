From Tuto1 Require Import Loader.

(*** Defining terms ***)

MyDefine n := 1.
Print n.

MyDefine f := (fun (x : Type) => x).
Print f.

MyDefine definition := 5.
Print definition.

MyDefine foo := (fun (T : Type) => forall (P : T -> Type) (t : T), P t).
Print foo.

(*** Reasoning about terms ***)

(* TODO note can assume no match statements, fixpoints, etc etc etc *)
(* TODO note constants etc limitatoins *)
(* TODO add more tests that are useful *)
Arity n. (* 0 *)
Arity f. (* 0 *)
Arity definition. (* 0 *)
Arity foo. (* 0 *)
Arity (foo nat). (* 0 *)
Arity (fun (n : nat) => n). (* 1 *)
Arity (fun (T : Type) (P : T -> Type) => forall (t : T), P t). (* 3 *)

Nargs (foo nat). (* 1 *)
Nargs (fun (x y : nat) => x + y). (* 0 *)
Nargs ((fun (x y : nat) => x + y) 1). (* 1 *)
Nargs ((fun (x y : nat) => x + y) 1 3). (* 2 *)
Nargs (((fun (x y : nat) => x + y) 1) 3). (* 2 *)


Count nat in body (foo nat). (* 1 *)
Count nat in body (fun (n : nat) => n). (* 0 *)
Count S in body 8. (* 8 *)
Count (fun (n : nat) => 1 + n) in body 8. (* 8 *)
(* TODO more tests *)

(*** Checking terms ***)

MyCheck 3.
MyCheck definition.
MyCheck (fun (x : Prop) => x).
MyCheck (fun (x : Type) => x).
MyCheck (forall (T : Type), T).
MyCheck (fun (T : Type) (t : T) => t).
MyCheck _.
MyCheck (Type : Type).

(*** Definitional Equality ***)

Equal 1 1.
Equal (fun (x : Type) => x) (fun (x : Type) => x).
Equal Type Type.
Equal 1 ((fun (x : nat) => x) 1).

Equal 1 2.
Equal (fun (x : Type) => x) (fun (x : Prop) => x).
Equal Type Prop.
Equal 1 ((fun (x : nat) => x) 2).
