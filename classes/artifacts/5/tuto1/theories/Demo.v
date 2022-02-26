From Tuto1 Require Import Loader.

(*** Interning terms ***)

Definition definition := 5.

Intern 3.
Intern definition.
Intern (fun (x : Prop) => x).
Intern (fun (x : Type) => x).
Intern (forall (T : Type), T).
Intern (fun (T : Type) (t : T) => t).
Intern _.
Intern (Type : Type).

(*** Defining terms ***)

MyDefine n := 1.
Print n.

MyDefine f := (fun (x : Type) => x).
Print f.

(*** Checking terms ***)

MyCheck 3.
MyCheck definition.
MyCheck (fun (x : Prop) => x).
MyCheck (fun (x : Type) => x).
MyCheck (forall (T : Type), T).
MyCheck (fun (T : Type) (t : T) => t).
MyCheck _.
MyCheck (Type : Type).

(*** Convertibility ***)

Convertible 1 1.
Convertible (fun (x : Type) => x) (fun (x : Type) => x).
Convertible Type Type.
Convertible 1 ((fun (x : nat) => x) 1).

Convertible 1 2.
Convertible (fun (x : Type) => x) (fun (x : Prop) => x).
Convertible Type Prop.
Convertible 1 ((fun (x : nat) => x) 2).
