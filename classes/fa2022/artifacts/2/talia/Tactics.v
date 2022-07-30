(*
 * CS 598 TLR
 * Artifact 2: Tactics
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
 * (or post in the forum if you're not here in person). It's also OK to
 * ask people in other groups.
 *
 * But again, as before, this is about the journey, not the destination.
 *
 * NOTE: To navigate this file, you will want to step down (the down arrow in the
 * top left corner) past definitions and proofs, step back up (the up arrow in the
 * top left corner) to back up, and step to a particular line using the go to
 * cursor button (the curved arrow in the top left corner). As you do that,
 * Coq will execute automation, and type check definitions and proofs.
 * The output will appear in the buffer on the right.
 *)

(*
 * Some built-in datatypes we'll use in this exercise (equality in Coq is included by default):
 *)
Require Import Nat. (* natural numbers *)
Require Import List. (* polymorphic lists *)
Require Import Ascii. (* characters *)

(*
 * Some syntax, separate from the datatype definitions:
 *)
Open Scope char_scope.
Import ListNotations.

(*
 * In addition to the tactics we'll see today, Coq has a notion of commands.
 * A command is kind of like a tactic, but it doesn't need to happen inside
 * of a proof, it can happen anywhere. These can produce new proofs, they can
 * print proofs for you, they can help you search for information, and they can
 * do a whole lot more. These are implemented inside of OCaml, either in Coq itself
 * or in plugins, which we'll see in later classes.
 *
 * Why does this matter right now? Well, in Coq, there's a nice command that lets
 * you print the definitions you just imported, and see how they're defined.
 *
 * So, for example, here's our list datatype:
 *)
Print list. (* polymorphic lists *)

(*
 * It is exactly like lists in Agda, albeit with less unicode :).
 * Though we still get the syntax [] for nil and :: for cons (two colons this time).
 *
 * This lets us define our example lists just like we did in Agda.
 * Note that in Coq, the type is not on a separate line from the definition;
 * it looks a lot more like OCaml whereas Agda looks a lot more like Haskell.
 * (This is no coincidence; Coq is implemented in OCaml, and Agda is implemented
 * in Haskell, so the communities are pretty tightly coupled).
 *)

(* The empty list of natural numbers *)
Definition empty_nat : list nat := [].

(* The empty list of characters *)
Definition empty_char : list ascii := [].

(* A list [1; 2; 3; 4] *)
Definition one_two_three_four : list nat :=
  [1; 2; 3; 4]. (* syntax for 1 :: 2 :: 3 :: 4 :: [] *)

(* A list [x; y; z] *)
Definition x_y_z : list ascii :=
  ["x"; "y"; "z"].

(*
 * NOTE: Since Coq notation is kept separately from the definitions, it is easy
 * to figure out how to expand the syntax, as long as you're inside of the IDE.
 * In CoqIDE, what you do is go to the View menu and uncheck "Display notations".
 * Give it a try right now.
 *)
Print empty_nat.
Print one_two_three_four.

(*
 * Now reenable syntax if you prefer (by checking "Display notations" in that same menu)---or
 * leave it as is if you'd rather see all syntax expanded. Your choice!
 *
 * Our length function is defined for us in the standard library, but I will
 * redefine it here to show it to you in more detail, and to minimize reliance on
 * the standard library for now. Let's define length:
 *)
Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | [] => 0 (* empty case *)
  | _ :: tl => S (length tl) (* cons case *)
  end.

(*
 * This is defined the same wqay as in Agda, but the pattern matching syntax is quite
 * different, and we must tell Coq explicitly to recurse by declaring a Fixpoint.
 *
 * Coq has a limited form of recursion, since it needs to terminate to avoid
 * paradoxes. Basically, one of the arguments needs to provably get smaller every time.
 * Like in our length definition, we recurse on only the tail of the list.
 * Coq checks this guard for recursion syntactically.
 *
 * Coq supports one thing Agda doesn't support natively---induction.
 * In addition to pattern matching and recursing over inductive types,
 * we can now induct over them. Every inductive time comes equipped with
 * an induction principle. The induction principle for nat looks exactly
 * like the way we induct over natural numbers in mathematics
 * (the "Check" command checks the type of its argument):
 *)
Check nat_rect.

(*
 * We have that for any P : nat -> Type (this is called the _inductive motive_),
 * if we have a proof of P 0, plus a proof that for any n, P n implies P (S n),
 * then we can construct a proof of forall n, P n.
 *
 * The induction principle for lists looks similar, but with nil in place of 0,
 * and cons in place of S, with some extra logic to deal with the new element consed
 * onto the list:
 *)
Check list_rect.

(*
 * For any type A and motive P : list A -> Type, if we have a proof of P [],
 * plus a proof that for any element a and list l, P l implies P (a :: l),
 * then we can construct a proof of forall (l : list A), P l.
 *
 * Induction and pattern matching plus syntactically guarded terminating recursion are
 * deeply and beautifully related to one another. You actually need only one or the other
 * in your language! Coq makes the decision to support recursion natively.
 * Then, every time you define a new inductive datatype, Coq automatically generates
 * induction principles defined in terms of recursion:
 *)
Print nat_rect.
Print list_rect.

(*
 * The first thing that's cool about this is that we can write our functions
 * using these induction principles. Here's an alternative way to define list length:
 *)
Definition length' {A : Type} (l : list A) : nat :=
  list_rect
    (fun _ => nat) (* motive *)
    O (* empty or base case*)
    (fun (a : A) (tl : list A) (length_tl : nat) =>
      (* cons or inductive case *)
      S length_tl)
    l. (* argument to induct over *)

(*
 * Take a second to look at these side-by-side.
 *)
Print length.
Print length'.

(*
 * The recursive argument---length tl in the original---is now generated automatically
 * in the inductive case. I've called it length_tl for the sake of making it easier
 * to relate to the original definition.
 *
 * The absolute coolest thing about this is that we get automation---by way of tactics---to
 * prove things by induction. By Curry-Howard, our length function is a proof, so we
 * can actually define the same we'd write a proof. Let's do that.
 *)
Theorem length'' {A : Type}:
  list A ->
  nat.
Proof.
  intros l. (* bind l : list A in our environment. *)
  induction l as [| h tl length_tl]. (* induct over l *)
  - apply 0. (* empty or base case *)
  - apply S. apply length_tl. (* cons or inductive case *)
Defined.

(*
 * Of course, there are many proofs that list A -> nat, and not all of them are the
 * length function. Some of them are quite boring. We could prove this theorem
 * by just returning 0 all the time, if we'd like. But the important thing here is
 * that tactics are really search procedures for proof terms. They sort of compile
 * to proof terms, if you will. So we can print our proof of length'':
 *)
Print length''.

(*
 * And see that it's the same as length'. Indeed:
 *)
Theorem length''_OK {A : Type}:
  forall (l : list A), length'' l = length' l.
Proof.
  intros l. reflexivity.
Qed.

(*
 * In general, we write "Qed" when we don't care about the content of our proof. That is,
 * when we don't want to use it like a program, and we care just about its type---the theorem
 * it proves---from here on out. We write "Defined" when we do care about the
 * content. Personally, I always write "Defined" in my own proofs, but I'm a weird
 * type theorist and nobody really likes us.
 *)

(*
 * EXERCISE 1: It's your turn to write some functions. Let's write app and rev like
 * we did in Agda last week---but let's use induction instead of recursion, and let's
 * write it using tactics. (This is something Coq programmers occasionally do,
 * though it's more common to write functions like app and rev directly.)
 *)

(* append two lists *)
Theorem app {A : Type} : 
  list A ->
  list A -> 
  list A. 
Proof.
  intros l1. (* bind l1 *)
  induction l1 as [| h tl app_tl]; intros l2. (* induct over l1, then bind l2 in both cases *)
  - apply l2. (* base case *)
  - apply (h :: app_tl l2). (* inductive case *)
Defined.

(* reverse a list *)
Theorem rev {A : Type} :
  list A ->
  list A.
Proof.
  intros l. (* bind l *)
  induction l as [| h tl rev_tl]. (* induct over l *)
  - apply []. (* base case *)
  - apply (app rev_tl [h]). (* inductive case *)
Defined.

(*
 * We can test your rev function like we did in Agda
 * (Example means the same thing as Theorem basically, it's just nice notation):
 *)

(* empty_nat doesn't change *)
Example rev_empty_nat_empty_nat : rev empty_nat = empty_nat.
Proof.
  reflexivity.
Defined.

(* empty_char doesn't change *)
Example rev_empty_char_empty_char : rev empty_char = empty_char.
Proof.
  reflexivity.
Defined.

(* [1; 2; 3; 4] becomes [4; 3; 2; 1] *)
Example rev_1_2_3_4_4_3_2_1 : rev one_two_three_four = [4; 3; 2; 1].
Proof.
  reflexivity.
Defined.

(* ["x"; "y"; "z"] becomes ["z"; "y"; "x"] *)
Example rev_x_y_z_z_y_x : rev x_y_z = ["z"; "y"; "x"].
Proof.
  reflexivity.
Defined.


(*
 * What does reflexivity do? It applies the refl constructor for the equality type,
 * much like we saw in Agda. In Coq, that constructor is called eq_refl:
 *)
Print rev_empty_nat_empty_nat.
Print rev_empty_char_empty_char.
Print rev_1_2_3_4_4_3_2_1.
Print rev_x_y_z_z_y_x.

(*
 * And the type is called eq:
 *)
Print eq.

(*
 * Actually, though, let's do better. We have a proof assistant---so why rely
 * just on testing? Here, we have reference implementations of append and reverse
 * inside of the standard library. So let's prove your reverse function correct.
 *
 * EXERCISE 2: I've given you the proof that my append function behaves the same as Coq's
 * append function. Write the proof that your reverse function behaves the same as Coq's
 * reverse function.
 *)

(* app is correct *)
Lemma app_OK {A : Type}:
  forall (l1 l2 : list A), app l1 l2 = List.app l1 l2.
Proof.
  intros. (* bind l1 and l2 *)
  induction l1. (* induct over l1 *)
  - reflexivity. (* these are computationally equal *)
  - simpl. (* reduce both sides neatly *)
    rewrite IHl1. (* use IHl1 to substitute (like subst in Agda) app l1 l2 with l1 ++ l2 *)
    reflexivity. (* these are computationally equal *)
Qed.

(* rev is correct *)
Lemma rev_OK {A : Type}:
  forall (l : list A), rev l = List.rev l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite IHl. rewrite app_OK. reflexivity.
Qed.

(*
 * There are two really cool things to note here. The first something quite beautiful
 * and general, which we saw in Agda last week---our proofs mirror the programs they're
 * about! And indeed, this mirrored structure exists at the term level, too (list_ind is
 * basically list_rect; the distinction doesn't matter for now, but ask if you're curious):
 *)
Print app.
Print app_OK.

(*
 * The second cool thing to note is that, while we (or at least I) used tactics that are super close
 * to the terms they produce, we can get a bit fancier if we'd like.
 * We can actually get _way_ fancier, as we'll see in later classes, and write our own
 * custom tactics and apply them in our proof. But also, Coq already has a bunch of
 * those defined for us, so we might as well use them. Like what if we don't want to
 * think about reflexivity, we just want to use something like "that looks obvious"?
 * How about:
 *)
Lemma app_OK' {A : Type}:
  forall (l1 l2 : list A), app l1 l2 = List.app l1 l2.
Proof.
  induction l1; simpl; congruence.
Qed.

(*
 * Woah woah woah what happened there? Well, congruence is an equality solver (we'll see 
 * these in future classes too!). It used this cute function, which is cong in Agda:
 *)
Check f_equal.

(*
 * And this, which is trans in Agda:
 *)
Check eq_trans.

(*
 * So we get a proof term that applies these for us and solves equalities:
 *)
Print app_OK'.

(*
 * Though this is different from the first proof we wrote, for the curious,
 * even though they prove the same theorem:
 *)
Print app_OK.

(*
 * Our first proof uses eq_ind_r (basically subst in Agda). The tactic "rewrite"
 * roughly generate a term that act like subst in Agda, though it is a bit more
 * powerful sometimes (and can sometimes give you scary looking terms because of that).
 *
 * Oh, by the way, about subst in Agda? There's something cute about it---I didn't
 * say it last week, but it's really an induction principle for the inductive equality
 * type. That's why in Coq, it's called eq_rect (or eq_ind), like we have list_rect
 * (or list_ind). And it's defined by matching over the equality type and destructing to
 * the singular reflexivity case:
 *)
Print eq_rect.

(*
 * Coq also defines inverses of eq_rect and eq_ind, which just swap x and y using
 * symmetry of equality:
 *)
Print eq_rect_r.

(*
 * NOTE: You can switch between eq_rect_r and eq_rect by using "rewrite <-" versus "rewrite"
 * (similarly for eq_ind). This is useful when you have some x = y as a hypothesis, and your
 * goal has a y in it, but you want an x in it.
 *
 * EXERCISE 3: Prove rev_OK again, but this time using heavier automation.
 * (If your first proof was already heavily automated, then expand it into something 
 * longer that applies each step explicitly.)
 *)

(* rev is still correct *)
Lemma rev_OK' {A : Type}:
  forall (l : list A), rev l = List.rev l.
Proof.
  induction l; auto; simpl; rewrite app_OK; congruence.
Qed.

(*
 * With all of that in mind, let's prove app_nil_l and app_nil_r.
 *
 * EXERCISES 4 and 5: Prove app_nil_l and app_nil_r.
 * You may reference the Agda proofs from last week if it helps.
 *)

(* left identity of nil for append *)
Theorem app_nil_l {A : Type}:
  forall (l : list A),
    app [] l = l.
Proof.
  intros. auto.
Qed.

(* right identity of nil for append *)
Theorem app_nil_r {A : Type}:
  forall (l : list A),
    app l [] = l.
Proof.
  intros. induction l; simpl; congruence.
Qed.

(*
 * Coq, like Agda, has symmetry of equality, and also a tactic for it:
 *)
Theorem app_nil_r_sym {A : Type} :
  forall (l : list A),
    l = app l [].
Proof.
  intros. symmetry. apply app_nil_r.
Qed.

(*
 * Though using fancier automation can let you avoid having to think about it, sometimes:
 *)
Theorem app_nil_r_sym' {A : Type} :
  forall (l : list A),
    l = app l [].
Proof.
  intros. auto using app_nil_r.
Qed.

(*
 * OK, now let's write the proof about reverse preserving the length function.
 *
 * NOTE: I'm omitting the lemma that helped you out last week---you can refer to the Agda
 * source if you want some help, or you can see organically why you might need to
 * cut a lemma. The latter is a really, really useful skill IRL, so I think it's
 * worth trying it that way.
 *
 * NOTE: There are also multiple ways to prove this. Like you can prove it like we did
 * in Agda last week, or you can use your proof of rev_OK to relate rev to Coq's List.rev,
 * then use functions in the Coq standard library. Either is fine! Both if you want.
 *
 * Exercise 6: Show that the reverse function preserves the length of the input list.
 *)

Lemma length_S_r {A : Type}:
  forall (l : list A) (a : A),
    length (app l (a :: [])) = S (length l).
Proof.
  induction l; simpl; congruence.
Qed.

Theorem rev_pres_length {A : Type}:
  forall (l : list A),
    length (rev l) = length l.
Proof.
  induction l; simpl; auto.
  rewrite length_S_r. congruence.
Qed.

(*
 * You're done with the proofs based on our Agda proofs last week! Some bonuses,
 * but if you don't have time, feel free to skip to the bottom.
 *
 * BONUS 1: Consider the alternative definition of rev defined below as rev_alt.
 * Prove rev_pres_length, but for this version of rev. How does it compare
 * to your old version of rev_pres_length? What changes? Why do you think this is?
 *
 * BONUS 2: Prove that rev and rev_alt behave the same way.
 *)

(* auxiliary function *)
Fixpoint rev_aux {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | h :: tl => rev_aux tl (h :: l2)
  end.

(* new definition of rev *)
Definition rev_alt {A : Type} (l : list A) := rev_aux l [].

Lemma rev_aux_pres_length {A : Type}:
  forall (l1 l2 : list A),
    length (rev_aux l1 l2) = length l1 + length l2.
Proof.
  induction l1; intros; auto.
  simpl. rewrite (IHl1 (a :: l2)). simpl.
  auto with arith.
Qed.

Theorem rev_pres_length_alt {A : Type}:
  forall (l : list A),
    length (rev_alt l) = length l.
Proof.
  induction l; simpl; auto.
  simpl. unfold rev_alt. rewrite rev_aux_pres_length. simpl.
  auto with arith.
Qed.

Lemma rev_aux_app {A : Type}:
  forall (l1 l2 : list A),
    rev_aux l1 l2 = rev l1 ++ l2.
Proof.
  induction l1; intros; auto.
  simpl in *. rewrite IHl1. 
  rewrite app_OK. rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma rev_rev_alt {A : Type}:
  forall (l : list A),
    rev_alt l = rev l.
Proof.
  intros l. unfold rev_alt. 
  rewrite rev_aux_app. apply List.app_nil_r.
Qed.

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

