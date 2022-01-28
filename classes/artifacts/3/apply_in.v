(*
 * CS 598 TLR
 * Artifact 3: Inside Iris Proof Mode
 * Student Copy
 *
 * In this exercise, you will work in groups of 4 to implement a new tactic inside of
 * Iris proof mode. It may help to look at the paper for details of how tactics are
 * implemented, and it may help to look at other tactic implementions inside of the
 * Iris source code. If you have Coq experience, please join a group of people who
 * do not have Coq experience outside of this class.
 *
 * This exercise comes from Robbert Krebbers. Only the discussion questions and comments
 * are mine. Likewise, this skeleton file is based on a solution he shared publicly,
 * which I'm happy to share after class. But as usual, you will be graded not on your
 * implementation, but on the discussion questions at the end. These questions will
 * be easier, not harder, if you really try to implement this yourself.
 * Still, if you have a lot of trouble with a proof, it's OK to ask me for help
 * (or post in the forum if you're not here in person, or ask me to hop into
 * your Zoom breakout). It's also OK to ask people in other groups.
 *
 * At the end of this class (or, if you're not attending,
 * sometime before 1230 PM the day of class) you'll post on the forum
 * about a discussion question you can find at the bottom of this file.
 * As always, it's about the journey, not the destination.
 *
 * OK, let's get started!
 *)
From iris.proofmode Require Import tactics.

(*
 * The tactic you will implement is called "iApply ... in", which is a real user
 * request in Iris proof mode. It's based on "apply ... in" from vanilla Coq.
 * That is, in Coq, we have the normal "apply" tactic, which applies a hypothesis to
 * refine a goal:
 *)
Lemma show_apply (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros H1 H2 H3. (* goal : R *)
  apply H2. (* goal : Q *)
  apply H1. (* goal : P *)
  exact H3. (* no more goals *)
Qed.

(*
 * Well, in Coq, we also have "apply ... in", which applies hypotheses inside of
 * other hypotheses, to refine those hypotheses rather than the goal:
 *)
Lemma show_apply_in (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros H1 H2 H3. (* H3 : P *)
  apply H1 in H3. (* H3 : Q *)
  apply H2 in H3. (* H3 : R *)
  exact H3. (* no more goals *)
Qed.

(*
 * Iris Proof Mode gives you an experience almost exactly like using Coq,
 * even though you're in a logic that can handle reasoning about concurrency.
 * Iris has "iApply" and "iExact" where Coq has "apply" and "exact":
 *)
Lemma show_iApply {PROP : bi} (P Q R : PROP) : (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "H1 H2 H3". (* goal : R *)
  iApply "H2". (* goal : Q *)
  iApply "H1". (* goal : P *)
  iExact "H3". (* no more goals *)
Qed.

(*
 * But Iris does not have "iApply ... in". Trying to use it will give you a syntax error.
 *
 * You will implement that today!
 *
 * NOTE: I floated a bit between having you implement a new Iris tactic or learn
 * how to use Iris. I went with the latter because you haven't really had a chance
 * to implement new automation yet, and this is a proof automation class after all.
 * I super recommend checking out the Iris tutorial (also a recommendation from 
 * Robbert Krebbers) if you want to get more of a feel for what using Iris Proof Mode
 * is like: https://gitlab.mpi-sws.org/iris/tutorial-popl21
 *
 * With that in mind, let's implement "iApply ... in", which behaves like "apply ... in"!
 *)
Module Export tac_apply_in.
  Import environments reduction bi.
  Local Open Scope lazy_bool_scope.

  (*
   * We will implement a restricted version of the tactic. The restricted version in
   * particular does not handle the additional intuitionistic context described in the
   * paper, and also cannot handle some hypotheses the full version can handle.
   * Extensions to the tactic are left as bonus problems!
   *
   * Remember that tactics in Iris Proof Mode are implemented
   * using a combination of logic programming and computational reflection.
   * So to define a new tactic, we will actually state and prove a Lemma in Coq, then
   * invoke it by ascribing it special syntax in Ltac.
   *
   * EXERCISE 1: Prove the lemma tac_apply_in, which is needed to implement
   * the tactic "iApply ... in" (thanks to Robbert Krebbers for the wonderful
   * comments about what the lemma actually proves, which I've modified a bit
   * to fit the restricted context).
   *)
  Lemma tac_apply_in {PROP : bi} (Δ : envs PROP) i j P1 P2 Q :
    (** Let us use [envs_lookup] to determine the type of hypothesis [i]. Here,
    [envs_lookup i Δ] is a partial function that looks up hypothesis [i]
    in proof mode context [Δ]. It returns a pair [(false, P1 -∗ P2)], where [false] 
    indicates that [i] is not in the intuitionistic part, and [P1 -∗ P2] is the type of [i]. *)
    envs_lookup i Δ = Some (false, P1 -∗ P2)%I ->
    (** Since spatial separation logic can only be used once, we remove [i]
    from the context [Δ] in case it is persistent. We call the resulting
    context [Δ']. *)
    let Δ' := envs_delete false i false Δ in
    (** Let us use [envs_lookup] again, but now to determine the type of [j]. *)
    envs_lookup j Δ' = Some (false, P1) →
    (** Now that we have obtained all information about the initial goal, let us
    determine the context of the resulting goal. For this we use the function
    [match envs_replace j false false (Esnoc Enil j P2) Δ'] which replaces
    hypothesis [j] with [j : P2]. Note that we use [Δ'], so [i] has already
    been removed if that is required.*)
    match envs_replace j false false (Esnoc Enil j P2) Δ' with
    | Some Δ'' =>
       (** Our resulting goal *)
       envs_entails Δ'' Q
    | None =>
       (** The function returns [None] if we try to use a name that is already
       in use. Since we replace [j] by [j], this is not going happen. We put
       [False] so that the lemma becomes trivial in that case. *)
       False
    end ->
    (** Our initial goal *)
    envs_entails Δ Q.
  Proof.
    (* I will start this proof for you by breaking the macth statement into cases *)
    rewrite envs_entails_eq. intros.
    remember (envs_replace _ _ _ _ _).
    destruct o.
    - (** The [Some Δ''] case. Your goal is to show [of_envs Δ -∗ Q]. The easiest way
      that I found to get there was to rewrite that goal by a number of lemmas about
      the environment and about wands in Iris until the goal became [of_envs e -∗ Q],
      at which point this held by our hypothesis H1.

      You will absolutely need lemmas for this---and they should all be defined for you.
      The lemma assoc will also likely be useful.
      If you have trouble finding these, please let me know.
      You can search for relevant lemmas like this:
      *)
      Search envs. (* functions and lemmas about the environment *)
      Search bi_entails. (* functions and lemmas about wands *)
      (** You may also find the tactic eauto useful, when you see lots of question marks
      (existential variables) that Coq is yet to infer. There are a number of tactics
      that are useful for existentials, and they can be finnicky sometimes---please ask
      if you need help!

      Your proof below:
      *)
      admit.
    - (** The [None] case. Your goal is to show that the hypothesis H1 is absurd.

      Your proof below:
      *)
      admit.
  Admitted. (* <- change to Qed *)

 (*
  * The next step is to define Ltac tactic notation to use that lemma automatically
  * within proofs. Before we do this, it's useful to see how the lemma is useful
  * inside of a proof. I've started such a proof off for you.
  *
  * EXERCISE 2: Finish the proof below, which manually uses tac_apply_in to
  * prove the goal, first by applying H1 in H3, then by applying H2 in H3.
  * The Iris Proof Mode tactics iIntros, pm_reflexivity, pm_reduce, and iExact
  * were all useful for me.
  *)
  Lemma use_apply_in {PROP : bi} (P Q R : PROP) : (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
  Proof.
    iIntros "H1 H2 H3".
    (* refine our goal using the lemma we just proved, applying H1 in H3: *)
    refine (tac_apply_in _ "H1" "H3" _ _ _ _ _ _).
    - (* [envs_lookup H1 Δ = Some (false, P -∗ Q)] holds by reflexivity *)
      pm_reflexivity.
    - (* [envs_lookup H3 Δ' = Some (false, P)] holds by reflexivity *)
      pm_reflexivity. 
    - (* reduce the goal *)
      pm_reduce.
      (* refine our goal using the lemma we just proved, applying H2 in H3: *)
      refine (tac_apply_in _ "H2" "H3" _ _ _ _ _ _).
      (* your tactics below: *)
      + admit.
      + admit.
      + admit.
  Admitted. (* <- change to Qed *)

  (*
   * This is quite cumbersome! But we can pull it out into a tactic.
   * I've started this off for you.
   *
   * EXERCISE 3: Finish the tactic definition for iApply in. 
   *)
  Tactic Notation "iApply" constr(H1) "in" constr(H2) := 
    refine (tac_apply_in _ H1 H2 _ _ _ _ _ _);
      [fail (* replace with a tactic that proves [envs_lookup H1 Δ = Some (false, P1 -∗ P2)%I] *)
      |fail (* replace with a tactic that proves [envs_lookup H2 Δ' = Some (false, P1)] *)
      |fail]. (* replace with a tactic that reduces the goal *)
End tac_apply_in.

(*
 * You've implemented apply_in! Congrats! Also, you've seen a development process
 * that often helps with writing generic automation: 1) write a proof using existing
 * tactics, then 2) pull out repetitive patterns of tactics into new tactics.
 *
 * If your tactic is correct the test below will go through:
 *)
Lemma test1 {PROP : bi} (P Q R : PROP) : (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "H1 H2 H3".
  iApply "H1" in "H3".
  iApply "H2" in "H3".
  iExact "H3".
Qed.

(*
 * BONUS 1: If you have extra time, try adding error handling to your iApply tactic
 * notation. You can write error messages by using the "fail" tactic, and passing
 * it any error message you'd like to print as a string:
 * https://coq.inria.fr/refman/proof-engine/ltac.html#coq:tacn.fail
 * And you can catch failing tactics for error handling using the "t1 || t2" tactical,
 * which tries the tactic "t1" and then, if "t1" fails, behaves like "t2":
 * https://coq.inria.fr/refman/proof-engine/ltac.html#first-tactic-to-make-progress.
 *)
Module Export tac_apply_in'.
  Import environments reduction bi.
  Local Open Scope lazy_bool_scope.

  Tactic Notation "iApply'" constr(H1) "in" constr(H2) :=
    fail "iApply " H1 "in " H2 " is not implemented". (* <- implement *)
End tac_apply_in'.

(*
 * Testing error messages:
 *)
Lemma test2 {PROP : bi} (P Q R : PROP) : (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "H1 H2 H3".
  (* test errors *)
  Fail iApply' "H6" in "H3". (* Should print your error message *)
  Fail iApply' "H1" in "H5". (* Should print your error message *)
  Fail iApply' "H3" in "H1". (* Should print your error message *)

  (* the rest of the proof should still work *)
  iApply' "H1" in "H3".
  iApply' "H2" in "H3".
  iExact "H3".
Qed.

(*
 * BONUS 2: If you have extra time, try implementing a tactic that chains 2 "iApply ... in"
 * tactics together.
 *)
Module Export tac_apply_in_2.
  Import environments reduction bi tac_apply_in.
  Local Open Scope lazy_bool_scope.

  Tactic Notation "iApply_2" constr(H1) constr(H2) "in" constr(H3) :=
    fail "iApply_2 is not implemented". (* <- implement *)
End tac_apply_in_2.

(*
 * Testing chaining:
 *)
Lemma test3 {PROP : bi} (P Q R : PROP) : (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "H1 H2 H3".
  iApply_2 "H1" "H2" in "H3".
  iExact "H3".
Qed.

(*
 * BONUS 3: Implement the more general version of iApply ... in below.
 * This gets rid of some restrictions we assumed for our original iApply ... in.
 * But this exercise is for the more adventurous, who want to learn more about Iris---I
 * couldn't easily figure it out in an hour or so, and my reference answer is from
 * Robbert Krebbers. 
 *)
Module Export tac_apply_in''.
  Import environments reduction bi.
  Local Open Scope lazy_bool_scope.

  (** This lemma corresponds to the tactic [iApply i in j]. Initial goal:
  
  i : P1 -∗ P2
  j : P1
  ...
  ------------∗
  Q
  
  Resulting goal:
  
  j : P2
  ...
  ------------∗
  Q
  
  Aside from [i], [j], and [Q], the lemma has the following parameters:
  
  - [Δ] is the whole proof mode context (a mapping from strings to Iris
    propositions)
  - [pi] and [pj] are Booleans that say if hypothesis [i] and [j] live in the
    intuitinistic (= true) or spatial (= false) context. Hypotheses in the
    intuitionistic context can be used multiple (or zero) times, whereas
    hypotheses in the spatial context need to be used exactly once.
  - [R] is the type of hypotheses [i]. The premise [IntoWand] later checks that
    it is indeed a wand [P1 -∗ P2]. *)

  Lemma tac_apply_in {PROP : bi} (Δ : envs PROP) i pi j pj P1 P2 R Q :
    (** Let us use [envs_lookup] to determine the type of hypothesis [i]. Here,
    [envs_lookup i Δ] is a partial function that looks up hypothesis [i]
    in proof mode context [Δ]. It returns a pair [(pi, R)], where [pi] indicates
    that [i] is in the intuitionistic part, and [R] is the type of [i]. *)
    envs_lookup i Δ = Some (pi, R) →
    (** Since spatial separation logic can only be used once, we remove [i]
    from the context [Δ] in case it is persistent. We call the resulting
    context [Δ']. *)
    let Δ' := envs_delete false i pi Δ in
    (** Let us use [envs_lookup] again, but now to determine the type of [j]. *)
    envs_lookup j Δ' = Some (pj, P1) →
    (** Let us ensure that R is indeed a wand. Ignoring [pi] and [pj], the
    [IntoWand] type class says [R ⊢ P1 -∗ P2]. *)
    IntoWand pi pj R P1 P2 →
    (** Now that we have obtained all information about the initial goal, let us
    determine the context of the resulting goal. For this we use the function
    [match envs_replace j pj (pi &&& pj) (Esnoc Enil j P2) Δ'] which replaces
    hypothesis [j] with [j : P2]. Note that we use [Δ'], so [i] has already
    been removed if that is required.*)
    match envs_replace j pj (pi &&& pj) (Esnoc Enil j P2) Δ' with
    | Some Δ'' =>
       (** Our resulting goal *)
       envs_entails Δ'' Q
    | None =>
       (** The function returns [None] if we try to use a name that is already
       in use. Since we replace [j] by [j], this is not going happen. We put
       [False] so that the lemma becomes trivial in that case. *)
       False
    end →
    (** Our initial goal *)
    envs_entails Δ Q.
  Proof.
    (* your proof here *)
  Admitted. (* <- replace with Qed *)

  Tactic Notation "iApply''" constr(H1) "in" constr(H2) :=
    fail "not implemented".
End tac_apply_in''.

(* Test more general version: *)
Lemma test4 {PROP : bi} (P Q R : PROP) : □ (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "#H1 H2 H3".
  (* test errors *)
  Fail iApply'' "H6" in "H3". (* Should print your error message *)
  Fail iApply'' "H1" in "H5". (* Should print your error message *)
  Fail iApply'' "H3" in "H1". (* Should print your error message *)

  (* test *)
  iApply'' "H1" in "H3".
  iApply'' "H2" in "H3".
  iExact "H3".
Qed.

(**
  That's it for now! When we have 25 minutes left of class, please do this:

    1. Turn to your group and discuss any one of the questions below.
    2. Post your answer─just one answer for your group, clearly indicating
       all members of the group. (If you are not here, and are working alone,
       you can post your answer alone.)
    3. With 10 minutes left, finish posting your answer, so we can discuss
       a bit as a class if time allows. We'll follow up on the discussion
       at the start of Tuesday's class.

  You'll be graded based on whether you post an answer, not based on
  what it is, so don't worry too much about saying something silly.

  DISCUSSION QUESTIONS (choose just one): 

  1. In this exercise, you implemented a tactic by first manually proving 
  a particular case (EXERCISE 2), then pulling your proof out into a general
  tactic (EXERCISE 3). Can you think of any tools one could implement to make
  that workflow easier? What would the user experience be? How might you implement
  such a tool?

  2. What was the most confusing part of implementing this tactic? What would you
  do to make it easier?

  3. Is there anything you preferred about this style of automation relative to
  other kinds of automation you've seen so far? Is there anything you preferred less?
  Why or why not?
 *)
