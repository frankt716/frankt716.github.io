(** * Predicate logic with equality
 *)

(** Formal language
    - Logical symbols: [True], [False], [/\], [\/], [->], [forall], [exists], and [=].
    - Predicate symbols: P, Q, R, etc
      - Think of a _predicate_ as a "parameterized"
        proposition, e.g.,
        - [P(x,y) := "x > y"]
        - [Q(x) := "x is mortal"]
        - [R(x,y,z) := "x + y = z"]
    - Variables: [x], [y], [z], etc
    - Terms: variables and constants are terms
    - Formulas:
      - [True], [False] are formulas.
      - If [R] is a predicate symbol in [n] variables, then
        [R x1 ... xn] is a formula.
      - If [P] and [Q] are formulas, then
        - [P /\ Q]
        - [P \/ Q]
        - [P -> Q]
        are formulas.
      - If [P x] is a formula and [x] is a variable of type [A],
        then
        - [forall x : A, P x]
        - [exists x : A, P x]
        are formulas.
      - If [a : A] and [b : A], then [a = b] is a formula.
 *)

(** * [forall] (comp: "polymorphic" function, logic: for all)
    - Introduction (function abstraction):
      - Computation: Given [x : A |- e : P x], we have
                     [fun x : A => e : forall x : A, P x].
      - Logic: To prove [forall x : A, P x], assume an
               arbitrary [x : A] and show [P x].
    - Elimination (function application):
      - Computation: Given [f : forall x : A, P x] and [a : A],
                     we have [f a : P a].
      - Elimination: If we know [forall x : A, P x], then
                     [P a] holds for any [a : A].
 *)

(** * [exists] (comp: "polymorphic" pair, logic: exists)
    - Introduction:
      - Computation: Given [a : A] and [prf : P a], we have
                     [(a, prf) : exists x : A, P x].
      - Logic: To show [exists x : A, P x], find an example [a : A]
               and a proof [prf : P a].
    - Elimination:
      - Computation: Given [pair : exists x : A, P x], we have
                     [pr1 pair : A] and [pr2 pair : P (pr1 pair)].
      - Logic: If we know [exists x : A, P x], then we know of an example
               [a : A] so that [P a] holds.
 *)

(** * [=] (logic: equality)
    - Introduction: Given [a : A], we have [refl : a = a].
    - Elimination: Given [eq : a = b], we can replace every [b]
                   with [a].
 *)

Section PredicateLogic.

Theorem eq_symmetric :
  forall (A : Set) (a b : A),
    a = b -> b = a.
Proof.
  intros A a b eq.
  destruct eq.
  reflexivity.
Qed.

Theorem eq_transitive :
  forall (A : Set) (a b c : A),
    a = b -> b = c -> a = c.
Proof.
  intros A a b c eq1 eq2.
  destruct eq1.
  destruct eq2.
  reflexivity.
Qed.

Theorem transport :
  forall (A : Set) (a b : A) (P : A -> Prop),
    a = b -> P a -> P b.
Proof.
  intros A a b P eq pa.
  rewrite <- eq.
  exact pa.
Qed.

Theorem ex_then_and :
  forall (A : Set) (P Q : A -> Prop),
  (exists x : A, P x /\ Q x) -> (exists x : A, P x) /\ (exists x : A, Q x).
Proof.
  intros A P Q [a [pa qa]].
  split.
  - exists a. (* exists a *)
    exact pa.
  - exists a.
    exact qa.
Qed.
  
Theorem ex_then_or :
  forall (A : Set) (P Q : A -> Prop),
    (exists x : A, P x \/ Q x) -> (exists x : A, P x) \/ (exists x : A, Q x).
Proof.
  intros A P Q [a [pa | qa]].
  - left.
    exists a.
    exact pa.
  - right.
    exists a.
    exact qa.
Qed.

Theorem or_then_ex :
  forall (A : Set) (P Q : A -> Prop),
    (exists x : A, P x) \/ (exists x : A, Q x) -> exists x : A, P x \/ Q x.
Proof.
  intros A P Q [[x pa] | [x qa]].
  - exists x.
    left.
    exact pa.
  - exists x.
    right.
    exact qa.
Qed.

Theorem fa_iff_and :
  forall (A : Set) (P Q : A -> Prop),
    (forall x : A, P x /\ Q x) <-> (forall x : A, P x) /\ (forall x : A, Q x).
Proof.
Qed.

Theorem fa_then_or :
  forall (A : Set) (P Q : A -> Prop),
    (forall x : A, P x) \/ (forall x : A, Q x) -> (forall x : A, P x \/ Q x).
Proof.
Qed.

Theorem fa_then_imp :
  forall (A : Set) (P Q : A -> Prop),
    (forall x : A, P x -> Q x) -> (forall x : A, P x) -> (forall x : A, Q x).
Proof.
  intros A P Q f g x.
  apply f.
  apply g.
Qed.

Theorem ex_then_not_fa_not :
  forall (A : Set) (P : A -> Prop),
    (exists x : A, P x) -> ~ forall x : A, ~ P x.
Proof.
Qed.  

Theorem and_not_then_ex :
  exists (A : Set) (P Q : A -> Prop),
    ~ ((exists x : A, P x) /\ (exists x : A, Q x) -> exists x : A, P x /\ Q x).
Proof.
  exists bool.
  exists (fun b => b = true).
  exists (fun b => b = false).
  intros f.
  assert (ext : exists x : bool, x = true). {
    exists true.
    reflexivity.
  }
  assert (exf : exists x : bool, x = false). {
    exists false.
    reflexivity.
  }
  destruct (f (conj ext exf)) as [b [eq1 eq2]].
  symmetry in eq1.
  destruct eq1.
  discriminate.
Qed.

Theorem forall_not_then_exists :
  exists (A : Set), forall (P : A -> Prop),
    ~ ((forall x : A, P x) -> exists x : A, P x).
Proof.
  exists Empty_set.
  intros P f.
  assert (fa : forall x : Empty_set, P x). {
    intros x.
    destruct x.
  }
  destruct (f fa) as [x _].
  destruct x.
Qed.

End PredicateLogic.
