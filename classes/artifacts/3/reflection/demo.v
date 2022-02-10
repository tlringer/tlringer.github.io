(*
 * Reflection demo
 * Based on a simplified version of this: http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html
 *)

(* --- Evenness type --- *)

(*
 * We'll look at proofs of evenness for this. To start, let us define an inductive
 * type that can be constructed whenever the number it depends on is even.
 *)
Inductive isEven : nat -> Prop :=
| Even_O : isEven O (* 0 is even *)
| Even_SS : forall n, isEven n -> isEven (S (S n)). (* for any even n, 2 + n is even *)

(* --- Proof by reflection --- *)

(*
 * The essence of proof by reflection is that we will make a decision procedure
 * (sometimes a semidecision procedure) for evenness. This decision procedure
 * is basically the meat of our tactic we will implement---by passing in a number
 * and computing, we get Some proof of evenness whenever n is even, and otherwise None.
 *)
Fixpoint check_even (n : nat) : option (isEven n) := match n with
| O => Some Even_O                  (* 0 is even *)
| 1 => None                         (* 1 is not even *)
| S (S n') =>                       (* is 2 + n' even? *)
    match check_even n' with        (* depends on whether n' is even *) 
    | Some p => Some (Even_SS n' p) (* if n' is even, then 2 + n' is even *)
    | _ => None                     (* otherwise, 2 + n' is not even *)
    end
end.

(*
 * To use this as a tactic, we need a way to wrap this into a term that proves
 * our goal whenever we have an even number, and otherwise gives us
 * a goal we can always prove (True). This is the _type_ of that term---the
 * proposition that we'll prove (either our goal or True):
 *)
Definition optionOutType (P : Prop) (o : option P) :=
  match o with      (* match over the result of our decision procedure *)
  | Some _ => P     (* if it returned some proof of P, then we will show our goal P *)
  | _ => True       (* otherwise, we'll show a tautology *)
  end.

Eval compute in (optionOutType (isEven 256) (check_even 256)).
Eval compute in (optionOutType (isEven 255) (check_even 255)).

(*
 * This is the wrapper term itself, which returns a proof of our goal when
 * we have one, and otherwise returns a proof of True:
 *)
Definition optionOut (P : Prop) (o : option P) : optionOutType P o :=
  match o with     (* match over the result of our decision procedure *)
  | Some pf => pf  (* if it returned some proof of P, then return that proof *)
  | _ => I         (* otherwise, prove True *)
  end.

Check (optionOut (isEven 256) (check_even 256)).
Eval compute in (optionOutType (isEven 256) (check_even 256)).

Check (optionOut (isEven 255) (check_even 255)).
Eval compute in (optionOutType (isEven 255) (check_even 255)).

(*
 * Our tactic uses "exact", so it works exactly when the goal is the type
 * of (optionOut (isEven N) (check_even N)). So for even numbers, we can
 * always prove they are even. But for odd numbers, we can only prove True!
 * And since we match over our goal, we can only run this tactic when our goal
 * is isEven N---so proving True is a no-op.
 *)
Ltac prove_even_reflective :=
match goal with
| [ |- isEven ?N] => exact (optionOut (isEven N) (check_even N))
end.

Theorem even_256 : isEven 256.
Proof.
  prove_even_reflective.
Defined.

Print even_256.

Theorem even_555 : isEven 255.
Proof.
  Fail prove_even_reflective. (* can only prove True *)
Abort.

Theorem true : True.
Proof.
  Fail prove_even_reflective. (* our goal isn't in the right form *)
Abort.

(*
 * The computation is inside of check_even
 *)

(* --- Compare to this --- *)

Theorem even_256' : isEven 256.
Proof.
  repeat constructor.
Defined.

Print even_256'.
Print even_256.

(* Still big if you normalize, but no need to *)
Eval compute in even_256.

(* --- Do note --- *)

Lemma theyre_the_same_picture :
  even_256 = even_256'.
Proof.
  reflexivity.
Qed.


