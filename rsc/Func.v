From Coq Require Import Bool.Bool.
(**
   Functions as relations.
 *)
Section Functions.
  Variable (choice : forall {A P} (prf : exists a : A, P a), A).
  Hypothesis (choice_ok : 
               forall {A P} (prf : exists a : A, P a), P (choice prf)).

  (**
     Functions can be realized as special binary relations.
     To specify a function from [dom] to [cod], specify
     a binary relation that is total and functional.
     Intuitively, [rel x y] means when we evaluate the function at [x]
     then the output is [y].
   *)
  Record Func (dom cod : Type) : Type :=
    mkFunc {
        rel : dom -> cod -> Prop
      ; total : forall x : dom, exists y : cod, rel x y
      ; functional : forall x : dom, forall y z : cod, rel x y -> rel x z -> y = z
      }.

  (**
     Totality says for any [x] in [dom] there is some [y] in [cod]
     such that [rel x y]. Thus, a natural notion of function application is
     to map [x] to [y].
   *)
  Definition app : forall {dom cod}, Func dom cod -> dom -> cod.
  Proof.
    intros dom cod f x.
    exact (choice (f.(total dom cod) x)).
  Defined.

  (**
     Indeed, this notion of function application agrees with the
     underlying relation of a given function.
   *)
  Lemma app_iff_rel : forall {dom cod} (f : Func dom cod) (x : dom) (y : cod),
      app f x = y <-> (f.(rel dom cod) x y).
  Proof.
    intros dom cod f x y.
    set (s := total dom cod f x).
    unfold app.
    fold s.
    split.
    - intros app.
      rewrite <- app.
      exact (choice_ok s).
    - intros rel.
      apply (f.(functional dom cod)) with (x := x).
      + exact (choice_ok s).
      + exact rel.
  Qed.

  (**
     Often, we define functions by "formulas". For example, we often
     write
     [[
     x ↦ x + 1
     ]]
     or
     [[
     f(x) = x + 1
     ]]
     to define a function that maps the input [x] to the output [x + 1].
     This always yields a function in the sense introduced in the
     beginning of this module.
   *)
  Definition by_formula : forall {dom cod : Type}, (dom -> cod) -> Func dom cod.
  Proof.
    intros dom cod f.
    refine (mkFunc dom cod (fun x y => f x = y) _ _).
    - intros x.
      exists (f x).
      reflexivity.
    - intros x y z eq1 eq2.
      rewrite <- eq1.
      rewrite <- eq2.
      reflexivity.
  Defined.

  (**
     Of course, the function defined by [by_formula] must agree with the given
     formula. For example, when I evaluate the function defined by
     [[
     x ↦ x + 1
     ]]
     at [1], I should get [2].
   *)
  Lemma by_formula_ok : forall {dom cod : Type} (formula : dom -> cod) (x : dom),
      app (by_formula formula) x = formula x.
  Proof.
    intros dom cod formula x.
    unfold by_formula.
    unfold app.
    simpl.
    set (ok := choice_ok
                 (ex_intro (fun y : cod => formula x = y) (formula x) eq_refl)).
    symmetry.
    exact ok.
  Qed.

  (**
     We consider two functions
     [[
     f, g : dom → cod
     ]]
     equal if they have the same IO behavior:
     they map the same input to the same output.
     This is called _functional extensionality_.
     Extensionality means that we don't care about the
     internals of the function. For example, the functions
     [[
     f(x) = 2(x + 1) and g(x) = 2x + 2
     ]]
     are equal (because they have the same IO behavior)
     even though their internals are different (they are defined
     by different formulas.)
   *)
  Hypothesis funext : forall {dom cod} (f g : Func dom cod),
      (forall x : dom, app f x = app g x) -> f = g.

  (**
     Given a function that maps elements of [A] to elements of [B]
     and a function that maps elements of [B] to elements of [C], we
     can compose these two functions, yielding a function that maps
     elements of [A] to elements of [C]. Function composition is given
     by the following formula:
     [[
     x ↦ app g (app f x)
     ]]
   *)
  Definition comp : forall {A B C}, Func B C -> Func A B -> Func A C.
  Proof.
    intros A B C g f.
    exact (by_formula (fun a => app g (app f a))).
  Defined.

  (**
     For any two composable functions, the composite agrees with the
     formula given above. This is a simple corollary of [by_formula_ok].
   *)
  Corollary comp_ok : forall {A B C} (g : Func B C) (f : Func A B) (a : A),
      app (comp g f) a = app g (app f a).
  Proof.
    intros A B C g f a.
    unfold comp.
    rewrite by_formula_ok.
    reflexivity.
  Qed.

  (**
     Function composition is associative.
   *)
  Lemma comp_assoc : forall {A B C D} (f : Func C D) (g : Func B C) (h : Func A B),
      comp f (comp g h) = comp (comp f g) h.
  Proof.
    intros A B C D f g h.
    apply funext.
    intros a.
    rewrite comp_ok.
    rewrite comp_ok.
    rewrite comp_ok.
    rewrite comp_ok.
    reflexivity.
  Qed.

  (**
     The identity function is sort of like a no-op in CS.
     Given an element of [A], the identity function on [A] simply
     outputs the input without doing anything to it.
     It is defined by the formula
     [[
     x ↦ x
     ]]
   *)
  Definition id : forall {A}, Func A A.
  Proof.
    intros A.
    exact (by_formula (fun x => x)).
  Defined.

  (**
     Again, [id_ok] is a simple corollary of [by_formula_ok]. Ignore
     the weird syntax of its statement. It is needed for minor
     technical reasons.
   *)
  Corollary id_ok : forall {A : Type} x, app (@id A) x = x.
  Proof.
    intros A x.
    unfold id.
    rewrite by_formula_ok.
    reflexivity.
  Qed.

  (**
     The identity function is the "multiplicative identity" with respect
     to composition.
   *)
  Theorem id_left : forall {dom cod} (f : Func dom cod), comp f id = f.
  Proof.
    intros dom cod f.
    apply funext.
    intros x.
    rewrite comp_ok.
    rewrite id_ok.
    reflexivity.
  Qed.

  Theorem id_right : forall {dom cod} (f : Func dom cod), comp id f = f.
  Proof.
    intros dom cod f.
    apply funext.
    intros x.
    rewrite comp_ok.
    rewrite id_ok.
    reflexivity.
  Qed.

  (**
     A _surjective_ function is a function in which every element
     in the codomain is mapped by some element in the domain.
   *)
  Definition surjective {dom cod} (f : Func dom cod) :=
    forall y : cod, exists x : dom, app f x = y.

  (**
     An _injective_ function is a function in which no two elements in the
     domain are mapped to the same element in the codomain.
   *)
  Definition injective {dom cod} (f : Func dom cod) :=
    forall x x' : dom, app f x = app f x' -> x = x'.

  (**
     A trivial surjective function is the identity function.
   *)
  Example id_sur : forall {A}, surjective (@id A).
  Proof.
    intros A a.
    exists a.
    rewrite id_ok.
    reflexivity.
  Qed.

  (**
     A trivial injective function is the identity function.
   *)
  Example id_inj : forall {A}, injective (@id A).
  Proof.
    intros A a a' eq.
    rewrite id_ok in eq.
    rewrite id_ok in eq.
    exact eq.
  Qed.

  (**
     Every surjective function is _right cancellable_.
   *)
  Theorem sur_then_rc :
    forall {A B} (f : Func A B),
      surjective f ->
      forall C (g h : Func B C), comp g f = comp h f -> g = h.
  Proof.
    intros A B f sur C g h eq.
    apply funext.
    intros b.
    destruct (sur b) as [a eq'].
    rewrite <- eq'.
    rewrite <- comp_ok.
    rewrite <- comp_ok.
    rewrite eq.
    reflexivity.
  Qed.

  (**
     Every injective function is _left cancellable_.
   *)
  Theorem inj_then_lc :
    forall {B C} (f : Func B C),
      injective f ->
      forall A (g h : Func A B), comp f g = comp f h -> g = h.
  Proof.
    intros B C f inj A g h eq.
    apply funext.
    intros a.
    apply inj.
    rewrite <- comp_ok.
    rewrite <- comp_ok.
    rewrite eq.
    reflexivity.
  Qed.

  (**
     A function [f : dom -> cod] is invertible if there is a
     function [g : cod -> dom] so that [comp f g = id] and
     [comp g f = id].
   *)
  Definition invertible {A B} (f : Func A B) :=
    exists g : Func B A, comp f g = id /\ comp g f = id.

  (**
     Every bijection is invertible.
   *)
  Theorem bij_then_inv :
    forall {A B} (f : Func A B), injective f -> surjective f -> invertible f.
  Proof.
    intros A B f inj sur.
    unfold invertible.
    unfold surjective in sur.
    exists (by_formula (fun b => choice (sur b))).
    split.
    - apply funext.
      intros b.
      rewrite comp_ok.
      rewrite by_formula_ok.
      set (eq := choice_ok (sur b)).
      simpl in eq.
      rewrite eq.
      rewrite id_ok.
      reflexivity.
    - apply funext.
      intros a.
      rewrite comp_ok.
      rewrite by_formula_ok.
      set (eq := choice_ok (sur (app f a))).
      simpl in eq.
      unfold injective in inj.
      apply inj in eq.
      rewrite id_ok.
      exact eq.
  Qed.

  (**
     The composition of two invertible functions is invertible.
   *)
  Theorem inv_closed_under_comp :
    forall {A B C} (g : Func B C) (f : Func A B),
      invertible g -> invertible f -> invertible (comp g f).
  Proof.
    intros A B C g f [gi [eq_g1 eq_g2]] [fi [eq_f1 eq_f2]].
    exists (comp fi gi).
    split.
    - rewrite comp_assoc.
      pattern (comp (comp g f) fi).
      rewrite <- comp_assoc.
      rewrite eq_f1.
      rewrite id_left.
      rewrite eq_g1.
      reflexivity.
    - rewrite comp_assoc.
      pattern (comp (comp fi gi) g).
      rewrite <- comp_assoc.
      rewrite eq_g2.
      rewrite id_left.
      rewrite eq_f2.
      reflexivity.
  Qed.

  (**
     Natural numbers consist of 0, 1, 2, .... every thing is
     represented as a binary number in a computer and every
     binary number corresponds to a natural number, so we
     can think of a program as a function [f : nat -> nat] that
     takes an input (represented as a natural number) and
     produces an output (represented as a natural number).
     Programs themselves are represented as binary numbers
     in a computer, i.e., every program can be given a
     natural number _code_. A particularly interesting
     function is the decoder [decode : nat -> (Func nat nat)], i.e.,
     it takes the natural number code of a program and
     outputs a function that the program computes. The following
     theorem shows that no function [f : nat -> (Func nat nat)] is
     surjective. In particular, this means that [decode] is not
     surjective, i.e., some functions can't be computed by any
     program. This proof employs a technique called _diagonalization_.
   *)
  Theorem uncomputable :
    forall (f : Func nat (Func nat nat)), ~ surjective f.
  Proof.
    intros f sur.
    set (k := by_formula (fun n => S (app (app f n) n))).
    destruct (sur k) as [n eq].
    set (m := app (app f n) n).
    assert (eq' : m = app k n).
    {
      unfold m.
      rewrite eq.
      reflexivity.
    }
    unfold k in eq'.
    rewrite by_formula_ok in eq'.
    fold m in eq'.
    set (neq := n_Sn m).
    contradiction.
  Qed.

  (**
     We can prove Cantor's theorem using the same technique
     as [uncomputable].
   *)
  Theorem cantor :
    forall {A} (f : Func A (Func A bool)), ~ surjective f.
  Proof.
    intros A f sur.
    set (g := by_formula (fun a => negb (app (app f a) a))).
    destruct (sur g) as [a eq].
    assert (eq' : app (app f a) a = app g a).
    {
      rewrite eq.
      reflexivity.
    }
    unfold g in eq'.
    rewrite by_formula_ok in eq'.
    symmetry in eq'.
    apply no_fixpoint_negb in eq'.
    contradiction.
  Qed.    

End Functions.
