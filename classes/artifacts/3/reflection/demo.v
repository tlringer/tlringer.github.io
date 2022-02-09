
Inductive isEven : nat -> Prop :=
| Even_O : isEven O
| Even_SS : forall n, isEven n -> isEven (S (S n)).

Fixpoint check_even (n : nat) : option (isEven n) := match n with
| O => Some Even_O
| 1 => None
| S (S n') =>
    match check_even n' with
    | Some p => Some (Even_SS n' p)
    | _ => None
    end
end.

Definition optionOutType (P : Prop) (o : option P) :=
  match o with
  | Some _ => P
  | _ => True
  end.

Definition optionOut (P : Prop) (o : option P) : optionOutType P o :=
  match o with
  | Some pf => pf
  | _ => I
  end.

Check (optionOut (isEven 256) (check_even 256)).
Eval compute in (optionOutType (isEven 256) (check_even 256)).

Check (optionOut (isEven 255) (check_even 255)).
Eval compute in (optionOutType (isEven 255) (check_even 255)).

Ltac prove_even_reflective :=
match goal with
| [ |- isEven ?N] => exact (optionOut (isEven N) (check_even N))
end.

Theorem even_256 : isEven 256.
Proof.
  prove_even_reflective.
Defined.

Theorem even_555 : isEven 255.
Proof.
  Fail prove_even_reflective. (* can only prove True *)
Abort.

(* Still big if you normalize, but no need to *)
Eval compute in (optionOut (isEven 256) (check_even 256)).

(*
 * The computation is inside of check_even
 *)

(* --- Compare to this --- *)

Theorem even_256' : isEven 256.
Proof.
  repeat constructor.
Defined.

Print even_256'.

(* --- Do note --- *)

Lemma theyre_the_same_picture :
  even_256 = even_256'.
Proof.
  reflexivity.
Qed.


