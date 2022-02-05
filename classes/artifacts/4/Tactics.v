(*
 * CS 598 TLR
 * Artifact 4: Custom Tactics in Ltac
 * Talia's Copy
 *
 * READ ME FIRST: This will be the same style as last week. That is, the emphasis is
 * on learning about the experience of using tactics and how they relate to
 * proof objects like you learned about last week. So you are graded for the discussion
 * question at the bottom of this file, and not on your ability to finish the proofs.
 *
 * At the end of this class (or, if you're not attending in person,
 * sometime before 1230 PM the day of class) you'll post on the forum
 * about what you found challenging, what you enjoyed, how the experience
 * compared to the experience from last week, and how you wish you could
 * improve the automation to make the experience better. 
 * If you or someone you're working with is a Coq wizard already,
 * and you know about automation that already exists that makes the
 * job easy, definitely take note of that and mention it as well.
 *
 * If you have a lot of trouble with a proof, it's OK to ask me for help
 * (or click the "ask for help" button on Zoom if you're not here in person).
 * It's also OK to ask people in other groups.
 *
 * But again, as before, this is about the journey, not the destination.
 *)

Require Import StructTact.StructTactics.

(*
 * We are going to start with just the natural numbers:
 *)
Require Import Nat.

(*
 * Let's define an addition function two ways, one recursing on the first number:
 *)
Fixpoint add_left (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add_left p m)
  end.

Fixpoint add_right (n m : nat) : nat :=
  match m with
  | O => n
  | S p => S (add_right n p)
  end.

(*
 * Proofs about add_left and add_right will follow more easily from induction
 * over the first and the second list, respectively. We will write a tactic
 * that does some of this choosing for us automatically! But before we get there,
 * let's write a couple of proofs that show this symmetry in action (TODO explain):
 *)
Lemma add_left_O :
  forall (n : nat),
    add_left n 0 = n.
Proof.
  induction n; simpl.
  - reflexivity.
  - find_higher_order_rewrite. reflexivity.
Qed.

Lemma add_right_O :
  forall (m : nat),
    add_right 0 m = m.
Proof.
  induction m; simpl.
  - reflexivity.
  - find_higher_order_rewrite. reflexivity.
Qed.

Lemma add_left_S :
  forall (n m : nat),
    S (add_left n m) = add_left n (S m).
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - find_higher_order_rewrite. reflexivity.
Qed.

(*
 * EXERCISE 1: TODO explain
 *)
Lemma add_right_S :
  forall (n m : nat),
    S (add_right n m) = add_right (S n) m.
Proof.
  induction m; intros; simpl.
  - reflexivity.
  - find_higher_order_rewrite. reflexivity.
Qed.

Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  induction n; intros; simpl.
  - symmetry. apply add_left_O.
  - find_higher_order_rewrite. apply add_left_S.
Qed.

(*
 * EXERCISE 2: TODO explain
 *)
Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  induction m; intros; simpl.
  - symmetry. apply add_right_O.
  - find_higher_order_rewrite. apply add_right_S.
Qed.

(*
 * The goal for this exercise is to write a tactic that chooses whether to induct
 * over n or m for us. That way, if someone swaps in add_left for add_right inside
 * of a proof development, all they have to do is substitute in the right
 * lemma names---the induction argument would not need to change.
 *
 * TODO explain
 * Exercise whatever
 *)
Print add_right.

(** TODO explain, mention number of args, propose extensions; find a way to infer args somehow *)
Ltac autoinduct_aux n m :=
  match goal with
  | [ |- context [ ?f _ _ ] ] =>
    lazymatch (eval red in f) with
    | (fix f n m {struct m} := @?body f n m) =>
      induction m
    | (fix f n m {struct n} := @?body f n m) =>
      induction n
    end
  end.

Ltac autoinduct :=
  lazymatch goal with
  | |- (forall n m, _) =>
    autoinduct_aux n m
  end. 

Lemma add_right_comm':
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  autoinduct; intros; simpl.
  - symmetry. apply add_right_O.
  - find_higher_order_rewrite. apply add_right_S.
Qed.

Lemma add_left_comm':
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  autoinduct; intros; simpl.
  - symmetry. apply add_left_O.
  - find_higher_order_rewrite. apply add_left_S.
Qed.

Print add_left_comm'.
Print add_right_comm'.

(*
 * That's it for now! You can keep playing with other proofs if you have
 * extra time. For example, it might be fun to define your own inductive types,
 * like a binary tree, and then write proofs about those types.
 *
 * If you have a lot of extra time, I recommend looking at the
 * Coq source code on Github to get a sense for how it's implemented:
 * https://github.com/coq/coq. In any case, when we have 25 minutes
 * left of class, please do this:
 *
 *  1. Turn to your group and discuss the question below.
 *  2. Post your answer─just one answer for your group, clearly indicating
 *     all members of the group. (If you are not here, and are working alone,
 *     you can post your answer alone.)
 *  3. With 10 minutes left, finish posting your answer, so we can discuss
 *     a bit as a class.
 *
 * You'll be graded based on whether you post an answer, not based on
 * what it is, so don't worry too much about saying something silly.
 *
 * DISCUSSION QUESTION: What was it like constructing these proofs using tactics,
 * relative to your experience using Agda last week? In your experience so far, what do you
 * think the tradeoffs are of writing proofs as terms versus using tactics?
 * What did you find challenging about this experience, if anything?
 * What did you find helpful, if anything? Did you get stuck at any point, and if so, 
 * where and why? Where do you wish you'd had more automation to help you out?
*)

