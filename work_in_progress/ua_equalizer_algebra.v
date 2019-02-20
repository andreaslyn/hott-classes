Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Sigma
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.theory.ua_homomorphism
  HoTTClasses.theory.ua_subalgebra
  HoTTClasses.theory.ua_first_isomorphism.

Import algebra_notations subalgebra_notations.

Section ump_subalgebra.
  Context
    `{Funext}
    {σ : Signature}
    {A B : Algebra σ}
    (P : SubalgebraPredicate A).

  Local Notation i := (hom_inclusion_subalgebra P).

  Definition inc_subimage (f : Homomorphism B A)
    := ∀ s (x : B s), P s (f s x).

  Definition hom_ump_1 (g : Homomorphism B (A&P)) : Homomorphism B A
    := hom_compose i g.

  Lemma inc_subimage_hom_ump_1 (g : Homomorphism B (A&P))
    : inc_subimage (hom_ump_1 g).
  Proof.
    intros s x.
    apply (g s x).
  Defined.

  Definition hom_ump_1' (g : Homomorphism B (A&P))
    : ∃ h : Homomorphism B A, inc_subimage h
    := (hom_ump_1 g ; inc_subimage_hom_ump_1 g).

  Lemma def_ump_factor_2 (f : ∃ h : Homomorphism B A, inc_subimage h)
    : ∀ s, B s → (A&P) s.
  Proof.
    intros s x.
    destruct f as [f F].
    specialize (F s x).
    exists (f s x).
    apply F.
  Defined.

  Lemma oppreserving_ump_factor_2 {w}
    (f : Homomorphism B A)
    (F : ∀ s (x : B s), P s (f s x))
    (ao : Operation A.(carriers) w)
    (bo : Operation B.(carriers) w)
    (C : ClosedUnderOp A P ao)
    (Q : OpPreserving f.(def_hom) bo ao)
    : OpPreserving (def_ump_factor_2 (f; F)) bo (op_subalgebra P ao C).
  Proof.
    induction w.
    - simpl in *.
      unfold def_ump_factor_2.
      simpl.
      apply path_sigma_hprop.
      simpl.
      apply Q.
    - simpl in *.
      intro x.
      apply IHw.
      unfold def_ump_factor_2.
      apply Q.
  Defined.

  Instance is_hom_ump_factor_2 (f : ∃ h : Homomorphism B A, inc_subimage h)
    : IsHomomorphism (def_ump_factor_2 f).
  Proof.
    intro u.
    apply oppreserving_ump_factor_2.
    apply is_homomorphism_hom.
  Defined.

  Definition hom_factor_2 (f : ∃ h : Homomorphism B A, inc_subimage h)
    : Homomorphism B (A&P)
    := BuildHomomorphism (def_ump_factor_2 f).

  Lemma ump_equalizer_1
    : (∃ h : Homomorphism B A, inc_subimage h)
      <~>
       Homomorphism B (A&P).
  Proof.
    apply (equiv_adjointify hom_factor_2 hom_ump_1').
    - intro f.
      apply path_homomorphism.
      intros s x.
      unfold hom_factor_2.
      simpl.
      unfold def_ump_factor_2, hom_ump_1'. simpl.
      reflexivity.
    - intros [f F].
      apply path_sigma_hprop.
      apply path_homomorphism.
      intros s x.
      unfold hom_ump_1', hom_factor_2. simpl.
      unfold def_inclusion_subalgebra, Compose. simpl.
      unfold def_ump_factor_2.
      reflexivity.
  Defined.

End ump_subalgebra.

Section equalizer.
  Context {σ} {A B : Algebra σ} (f g : Homomorphism A B).

  Definition def_predicate_equalizer (s : Sort σ) (x : A s) : hProp
    := BuildhProp (f s x = g s x).

  Global Instance is_closed_under_ops_predicate_equalizer
    : IsClosedUnderOps A def_predicate_equalizer.
  Proof.
    intro u.
    generalize (is_homomorphism_hom f u).
    generalize (is_homomorphism_hom g u).
    set (ao := u^^A).
    set (bo := u^^B).
    clearbody ao bo.
    intros F G.
    induction (σ u).
    - simpl. simpl in *. exact (G @ F^).
    - simpl. intros x p.
      apply (IHs (ao x) (bo (f t x))).
      + simpl. rewrite p. apply F.
      + simpl. apply G.
  Defined.

  Definition predicate_equalizer : SubalgebraPredicate A
    := BuildSubalgebraPredicate def_predicate_equalizer.

  Lemma isequal (s : Sort σ)
    : f s ∘ hom_inclusion_subalgebra predicate_equalizer s
    == g s ∘ hom_inclusion_subalgebra predicate_equalizer s.
  Proof.
    intro C.
    unfold hom_inclusion_subalgebra, def_inclusion_subalgebra.
    simpl in *.
    unfold Compose.
    destruct C as [D P].
    simpl.
    apply P.  
  Defined.

  Definition test1 (X : Algebra σ) :
    (∃ z : Homomorphism X A,
     ∀ (s : Sort σ),
     f s ∘ z s == g s ∘ z s)
    → ∀ s, X s → (A & predicate_equalizer) s.
  Proof.
    intros [z F] s C. specialize (F s C).
    exists (z s C).
    apply F.
  Defined.

  Instance is_homomorphism_test1 (X : Algebra σ)
    (E : ∃ z : Homomorphism X A,
          ∀ (s : Sort σ),
          f s ∘ z s == g s ∘ z s)
    : IsHomomorphism (test1 X E).
  Proof.
    intro u.
    unfold Subalgebra.
    simpl.
    unfold ops_subalgebra.
    simpl.
    set (cl := (closed_under_ops A def_predicate_equalizer u)).
    clearbody cl.
    generalize dependent cl.
    destruct E as [h E].
    generalize (is_homomorphism_hom h u).
    set (ao := u^^A).
    clearbody ao.
    set (xo := u^^X).
    clearbody xo.
    intros H C.
    induction (σ u).
    - simpl in *.
      apply path_sigma_hprop.
      simpl.
      apply H.
    - simpl in *.
      intro x.
      apply IHs.
      apply H.
  Defined.
    
  Definition hom_test1 (X : Algebra σ)
    (E : ∃ z : Homomorphism X A,
          ∀ (s : Sort σ),
          f s ∘ z s == g s ∘ z s)
    : Homomorphism X (A & predicate_equalizer)
    := BuildHomomorphism (test1 X E).

  Definition hom_test2 (X : Algebra σ)
    (h : Homomorphism X (A & predicate_equalizer)) :
    Homomorphism X A
  := hom_compose (hom_inclusion_subalgebra predicate_equalizer) h.

  Lemma test2_preserve (X : Algebra σ)
    (h : Homomorphism X (A & predicate_equalizer)) (s : Sort σ)
    : f s ∘ hom_test2 X h s == g s ∘ hom_test2 X h s.
  Proof.
    intro C.
    apply isequal.
  Defined.

  Definition hom_test2' (X : Algebra σ)
    (h : Homomorphism X (A & predicate_equalizer)) :
    (∃ z : Homomorphism X A,
          ∀ (s : Sort σ),
          f s ∘ z s == g s ∘ z s).
  Proof.
    exists (hom_test2 X h).
    intro s.
    apply test2_preserve.
  Defined.

  Lemma ump_equalizer `{Funext} (X : Algebra σ)
    : (∃ z : Homomorphism X A,
       ∀ (s : Sort σ),
       f s ∘ z s == g s ∘ z s)
      <~>
       Homomorphism X (A & predicate_equalizer).
  Proof.
    apply (equiv_adjointify (hom_test1 X) (hom_test2' X)).
    - intro h.
      apply path_homomorphism.
      intros s x.
      unfold hom_test1.
      unfold hom_test2'.
      simpl.
      unfold test1.
      simpl.
      unfold def_inclusion_subalgebra.
      unfold Compose.
      simpl.
      apply path_sigma_hprop.
      reflexivity.
    - intros [h E].
      apply path_sigma_hprop.
      apply path_homomorphism.
      intros s x.
      unfold hom_test1.
      unfold hom_test2'.
      simpl.
      unfold def_inclusion_subalgebra, test1, Compose.
      reflexivity.
    Defined.

End equalizer.
