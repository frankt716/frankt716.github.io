(** * Propositional Logic
    - A formal language + deduction rules
    - Many different interpretations (focus on the computational one)
 *)

(** * Formal language
    - Logical symbols: [True], [False], [/\], [\/], [->]
    - Propositional variables (atomic stuff):
        [is-raining], [is-sunny], [P], [Q], etc
    - Propositions:
        - [True], [False] are props.
        - Prop vars are props.
        - If [P] & [Q] are props, then [P /\ Q], [P \/ Q], [P -> Q] are props.
 *)

(** * How to read props
    - Right associative
    - Precedence: [/\] = [\/] > [->]
 *)

(** * Deduction rules
    The meaning of a logical symbol is given by
    - canonical proof (introduction)
    - canonical use (elimination)
 *)

(** * Computational content
    - Props as data types.
    - Data types describe computational phenomena.
    - Introduction = how to effect a comp phenomenon.
    - Elimination = how to use a comp phenomenon.
    - [t : T] means [t] has type [T].
    - [x : T1 |- t : T2] means [t] has type [T2] assuming [x] has type [T1].
 *)

(** * [True] (comp: trivial computation, logic: true)
    - Introduction:
        - computation: trivial computation is trivial [trivial : True].
        - logic: [True] is self evident.
    - Elimination: none.
 *)

(** * [False] (comp: impossible computation, logic: false)
    - Introduction: none
    - Elimination:
        - computation: given [absurd : False] we have [contradiction : P].
        - logic: a false hypothesis entails anything.
 *)

(** * [/\]  (comp: pair, logic: and)
    - Introduction:
        - computation: given [p : P] and [q : Q], we have [(p, q) : P /\ Q].
        - logic: to prove [P /\ Q], prove [P] and [Q].
    - Elimination:
        - computation: Given [pair : P /\ Q], we have [pr1 pair : P]
                       and [pr2 pair : Q].
        - logic: if I know [P /\ Q] then I know [P] and I know [Q].
 *)

(** * [\/] (comp: variant, logic: or)
    - Introduction:
        - computation:
            1. given [p : P], we have [left p : P \/ Q].
            2. given [q : Q], we have [right q : P \/ Q].
        - logic: to prove [P \/ Q], prove either [P] or [Q].
    - Elimination: case analysis.
        - computation: given [z : P \/ Q], [x : P |- r1 : R],
                       and [y : Q |- r2 : R], we have
                       [match z as x => r1 | y => r2 : R].
        - logic: if I know [P \/ Q] and I want to prove [R], then prove
                 [R] assuming [P] and prove [R] assuming [Q].
    - the elimination rule is similar to the _switch_ (in Coq it is _match_)
      construct in many programming languages.
 *)

(** * [->] (comp: function, logic: implication)
    - Introduction: function abstraction
        - computation: given [x : P |- e : Q], we have [fun x => e : P -> Q].
        - logic: to prove [P -> Q], assume [P] and derive [Q].
    - Elimination: function application
        - computation: given [f : P -> Q] and [p : P], we have [f p : Q].
        - logic: if I know [P -> Q], then, to prove [Q],
                 it suffices to prove [P].
 *)

(** * Examples
 *)
Section PropositionalLogic.
Variables P Q R : Prop.

Theorem curry_uncurry : ((P /\ Q) -> R) <-> (P -> (Q -> R)).
Proof.
  split.
  - intros f p q.
    apply f.
    split.
    + exact p.
    + exact q.
  - intros f [p q].
    apply f.
    + exact p.
    + exact q.
Qed.

Theorem and_uni : (P -> Q /\ R) <-> (P -> Q) /\ (P -> R).
Proof.
  split.
  - intros f.
    split.
    + intros p.
      apply f in p.
      destruct p as [q _].
      exact q.
    + intros p.
      apply f in p.
      destruct p as [_ r].
      exact r.
  - intros [f g] p.
    split.
    + apply f.
      exact p.
    + apply g.
      exact p.
Qed.

Theorem modus_tollens : (P -> Q) -> ~ Q -> ~ P.
Proof.
  intros f nq p.
  apply nq.
  apply f.
  exact p.
Qed.

Theorem resolution : (P \/ Q) -> (~ P \/ R) -> Q \/ R.
Proof.
  intros [p | q] [np | r].
  - contradiction.
  - right.
    exact r.
  - left.
    exact q.
  - left. (* [right] also works *)
    exact q. (* resp., [exact r] also works *)
Qed.
End PropositionalLogic.


(**
 Tells Coq to print implicit parentheses.
 Useful for learning precedence.
*)
Set Printing Parentheses.
Section AndExamples.
Variables P Q R : Prop.

Theorem proj1 : P /\ Q -> P.
Proof.
  intros [p q].
  exact p.
Qed.

(* [/\] is /\ *)
Theorem proj2 : P /\ Q -> Q.
Proof.
  intros [p q].
  exact q.
Qed.

Theorem and_comm :
  P /\ Q -> Q /\ P.
Proof.
  intros [p q].
  split.
  - exact q.
  - exact p.
Qed.

Theorem and_assoc :
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros [p [q r]].
  split.
  - split.
    + exact p.
    + exact q.
  - exact r.
Qed.

Theorem and_addition :
  P -> P /\ P.
Proof.
  intros p.
  split.
  - exact p.
  - exact p.
Qed.
  
End AndExamples.



Section OrExamples.
Variables P Q R : Prop.

Theorem or_comm :
  P \/ Q -> Q \/ P.
Proof.
  intros [p | q].
  - right.
    exact p.
  - left.
    exact q.
Qed.

Theorem or_assoc :
  P \/ (Q \/ R) -> (P \/ Q) \/ R.
Proof.
  intros [p | [q | r]].
  - left.
    left.
    exact p.
  - left.
    right.
    exact q.
  - right.
    exact r.
Qed.

Theorem noncontradiction :
  P -> ~ ~ P.
Proof.
  intros p.
  intros np.
  contradiction.
Qed.

Theorem demorgan :
  ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  split.
  - intros f.
    split.
    + intros p.
      apply f.
      left.
      exact p.
    + intros q.
      apply f.
      right.
      exact q.
  - intros [np nq] [p | q].
    + contradiction.
    + contradiction. 
Qed.
End OrExamples.



Section IffExamples.
Variables P Q : Prop.

Theorem iff_refl :
  P <-> P.
Proof.
  apply and_addition.
  intros p.
  exact p.
Qed.

Theorem iff_sym :
  (P <-> Q) -> (Q <-> P).
Proof.
  apply and_comm.
Qed.
  
End IffExamples.
