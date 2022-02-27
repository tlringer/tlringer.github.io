From Tuto1 Require Import Loader.

(*** Defining terms ***)

MyDefine n := 1.
Print n.

MyDefine f := (fun (x : Type) => x).
Print f.

MyDefine definition := 5.
Print definition.

MyDefine foo := (forall (T : Type) (P : T -> Type) (t : T), P t).

(*** Reasoning about terms ***)

Depth n. (* 0 *)
Depth f. (* 1 *)
Depth definition. (* 0 *)
Depth foo. (* 3 *)

(* Only supports definitions for now *)
Fail Depth (fun (n : nat) => n).

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
