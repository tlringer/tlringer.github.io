-- if curious: https://agda.readthedocs.io/en/v2.6.0.1/language/without-k.html
{-# OPTIONS --without-K --safe #-}

{-
  CS 598 TLR
  Artifact 1: Proof Objects
  Talia's Answer Key
-}
module proof-objects where

{-
  Some built-in datatypes we'll use in this exercise:
-}
open import Agda.Builtin.Nat -- natural numbers
open import Agda.Builtin.List -- polymorphic lists
open import Agda.Builtin.Char -- characters
open import Agda.Builtin.Equality -- equality

{-
  You can see these definitions by clicking them and then pressing the Alt
  key along with the period. Or you can use the middle button of your mouse,
  if you have one.

  For example, if we click on Agda.Builtin.List and press the Alt key
  along with the period, it will open up the file that defines the
  list datatype. A polymorphic list in Agda is defined a lot like the
  list datatype in Coq that we saw in the slides for the first class.
  It is an inductive datatype with two cases:

    data List (A : Set) : Set where
      []  : List A
      _∷_ : A → List A → List A

  In other words, as in Coq, a list is either empty ([]) or the result
  of consing (∷) an element of type A in front of some other list of
  elements of type A.

  For example, let's define some empty lists of numbers and characters.
  In Agda, a definition has its type on the first line, and then the
  term with that type on the next line:
-}

-- The empty list of natural numbers
empty-nat : List Nat -- the type
empty-nat = [] -- the term

-- The empty list of characters
empty-char : List Char -- the type
empty-char = [] -- the term

{-
  Cool. Now let's define some non-empty lists.

  NOTE: The Agda community has an unfortunate obsession with Unicode.
  The syntax for the cons constructor in Coq is two colons, written ::.
  Confusingly, the Agda cons constructor is actually denoted with a
  single special unicode character, written ∷. You can write this
  special character by typing \:: (with two colons), and it will
  magically turn into ∷.

  OK, with that in mind:
-}

-- A list [1; 2; 3; 4]
1-2-3-4 : List Nat -- type
1-2-3-4 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] -- term

-- A list [x; y; z]
x-y-z : List Char -- type
x-y-z = 'x' ∷ 'y' ∷ 'z' ∷ [] -- term

{-
  As in Coq, we can write functions about lists, like our length function,
  which we define by pattern matching. The syntax for pattern matching in
  Agda is defining each case on a different line:
-}

-- list length
length : forall {A : Set} -> List A -> Nat -- type
length [] = 0 -- term in the empty case
length (h ∷ tl) = suc (length tl) -- term in the cons case

{-
  That is, the length of the empty list ([]) is zero (0), and the
  length any other list (h ∷ tl) is one plus (suc, for "successor")
  the length of the tail of the list (length tl).

  EXERCISE 1: Write a function that reverses a list.
  You may use the function app I've written for you below,
  which appends two lists.
-}

-- list append
app : forall {A : Set} -> List A -> List A -> List A -- type
app [] l = l -- term in the empty case
app (h ∷ tl) l = h ∷ app tl l -- term in the cons case 

-- list rev
rev : forall {A : Set} -> List A -> List A -- type
rev [] = [] -- term in the empty case
rev (t ∷ ts) = app (rev ts) (t ∷ []) -- term in the cons case

{-
  Let's test your rev function.
  We're going to check that, on the lists we've defined at the top
  of this file, the result of calling rev gives us the reverse lists.

  To do that, we need a way to state what it means for two things to be
  equal. Equality in Agda is written ≡, which is typed as \== using the same
  magic as before, because of the community's unicode obsession:
  
    data _≡_ {a} {A : Set a} (x : A) : A → Set a where
      refl : x ≡ x

  Equality is an inductive datatype, just like lists. But one thing that's
  cool about the equality type is that it's something called a dependent type.
  A dependent type is a lot like a polymorphic type, but instead of taking
  a type argument (like the A in List A), it takes a _term_ argument
  (like the x in x ≡ x). Dependent types can refer to values!
  So we can define the type of all terms that prove our lists
  behave the way we want them to. And then we can write terms that
  have those types─our proofs.

  There is exactly one constructor for the equality type in Agda:
  refl, for reflexivity. Two things are equal by reflexivity when they
  compute to the same result. So if your rev function is correct,
  these test cases should compile:
-}

-- empty-nat doesn't change
rev-empty-nat-empty-nat : rev empty-nat ≡ empty-nat
rev-empty-nat-empty-nat = refl

-- empty-char doesn't change
rev-empty-char-empty-char : rev empty-char ≡ empty-char
rev-empty-char-empty-char = refl

-- [1; 2; 3; 4] becomes [4; 3; 2; 1]
rev-1-2-3-4-4-3-2-1 : rev 1-2-3-4 ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
rev-1-2-3-4-4-3-2-1 = refl

-- [x; y; z] becomes [z; y; x]
rev-x-y-z-z-y-x : rev x-y-z ≡ 'z' ∷ 'y' ∷ 'x' ∷ []
rev-x-y-z-z-y-x = refl

{-
  These test cases are actually proofs! Even though they all hold
  by computation (reflexivity), they are terms, just like the lists
  we refer to inside of them. Their types are the theorems that they prove.
  
  That's the beauty of Curry-Howard; our terms here are proof objects
  that prove the theorems stated by the types they inhabit.
  These programs are proofs!

  So now it's your turn to test my length function and, in the process,
  write some proofs yourself.

  EXERCISE 2: Prove that 1-2-3-4 and x-y-z have the right lengths.
-}

-- 1-2-3-4 has the right length
length-1-2-3-4-OK : length 1-2-3-4 ≡ 4
length-1-2-3-4-OK = refl

-- x-y-z has the right length
length-x-y-z-OK : length x-y-z ≡ 3
length-x-y-z-OK = refl

{-
  Those proofs are very small proofs that hold by computation.
  But what about when we want to get a bit fancier?
  
  For example, we might want to show that the list rev function
  preserves the length of the input. We can't do that by reflexivity!
  If you try it, you'll get a type error, which will say something
  scary like this:

    rev l != l of type List A
    when checking that the expression refl has type
    length (rev l) ≡ length l

  What gives? Well, the problem here is that while this equality is always
  true, Agda can't figure it out just plugging in the list l and running
  its computation or reduction rules. It can't solve that equality
  computationally. It needs us to guide it, instead.

  This is the distinction between _definitional_ and _propositional_ equality.
  Two things are definitionally equal if they compute to the same result;
  two things are propositionally equal if we can prove that they are equal.
  In Agda, Coq, and Lean, two things that are definitionally equal are
  necessarily propositionally equal, but the reverse is not necessarily true.

  ASIDE: Definitional equality is─for many proof assistants we care about in
  this class─a decidable judgment that follows from a few reduction rules,
  like unfolding some constants (δ-expansion), applying functions to
  arguments (Β-reduction ,which is sometimes called ι-reduction for
  inductive datatypes), renaming (α-conversion), and more.

  These may sound familiar if you're familiar with the λ-calculus,
  a simple functional programming language that is often used as an example
  in programming languages courses. The proof assistants Agda, Coq, and Lean
  all build on extensions of the λ-calculus with not just simple types,
  but also polymorphism (like the A in list A), dependent types (like the
  x in x ≡ x), and inductive types (like the list and ≡ datatypes themselves).
  
  But if you haven't heard of these, that's OK. I super recommend reading this
  chapter of Certified Programming with Dependent Types by Adam Chlipala:
  http://adam.chlipala.net/cpdt/html/Equality.html. If you'd like more
  information, that will really help─though it's in Coq. I hope to
  show you some automation that steps through equalities like this next week.
  
  BACK TO BUSINESS: The important point here for now is that just applying
  the refl constructor doesn't construct the proof we want, because these
  computation rules can't figure out the equality. But our theorem is still
  true, and indeed provable! But we need to get a bit fancier.
  We'll define a proof we need for the successor case first─as a lemma:
-}


-- TODO that's gross we can simplify ... show with rewrite
-- TODO and/or define a lemma first when showing, e.g. cong or subst... yeah do that
-- from the pfla/stdlib probably:
-- TODO move some of the eq proofs into exercises
cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {A : Set} {x y : A} (P : A -> Set) -> x ≡ y -> P x -> P y
subst P refl px = px

-- TODO don't need this yet but maybe ask for it? same with transitivity
sym : ∀ {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl  =  refl

-- TODO move this up, and start by showing just this, to avoid having to explain why we need a lemma ... 
-- TODO also note the type inference here. also clean and explain the with stuff
-- TODO split proposition or use inference or something... how to holes work
-- TODO show interactive mode a bit to help people figure things out
length-succ-r : ∀ {A} -> (l : List A) -> (a : A) -> length (app l (a ∷ [])) ≡ suc (length l)
length-succ-r [] a = refl  -- base case
length-succ-r {A} (h ∷ tl) a = cong suc (subst (λ (n : Nat) -> n ≡ suc (length tl)) refl (length-succ-r tl a))

-- TODO start with an easier subst lemma---really break this up into lemmas, and use the holes to help (explain the way this works with C-c C-,
 
-- TODO
rev-pres-length : forall {A} -> (l : List A) -> length (rev l) ≡ length l
rev-pres-length [] = refl -- base case
rev-pres-length (h ∷ tl) = trans (length-succ-r (rev tl) h) (cong suc (rev-pres-length tl))

-- TODO bonus if time: permutation etc, check that rev is a permutation

-- TODO rev involutive
rev-involutive : forall {A} -> (l : List A) -> rev (rev l) ≡ l
rev-involutive [] = refl
rev-involutive (h ∷ tl) = {!  !} -- rev (app (rev tl) (h ∷ [])) ≡ h ∷ tl
{-
 TODO app_nil_l and app_nil_r, what happens?
-}


{-
  Discussion questions:

  1. what was frustrating, and where do you want automation
  2. something about explicit proof objects in Agda
  3. some languages and proof assistants don't draw any distinction
  between definitional and propositional equality, and leave all equality
  checking to the proof checker. can you think of any possible tradeoffs there
  4. anything else you'd like to comment on or ask
  5. check the rest of the things want to cover, and ask questions about
  6. pattern matching and induction
  7. question about addition with app_nil_l and app_nil_r problem,
  defining addition differently, what it means.
  8. something about TCB
  9. something about de Bruijn

  if extra time, keep playing around, prove whatever you want lol
-}
