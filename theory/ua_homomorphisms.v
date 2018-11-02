Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.canonical_names
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.universal_algebra.

Section contents.
  Variable σ: Signature.

  Notation OpType := (OpType (sorts σ)).

  Section homo.
  Context (A B: sorts σ → Type)
    `{A_ops : AlgebraOps σ A} `{B_ops : AlgebraOps σ B}.

  Section with_f.
    Context (f : ∀ a, A a → B a).

    Arguments f {a} _.

    Fixpoint Preservation {n : OpType}: op_type A n → op_type B n → Type :=
      match n with
      | ne_list.one d => λ oA oB, f oA = oB
      | ne_list.cons x y => λ oA oB, ∀ x, Preservation (oA x) (oB (f x))
      end.

    Class HomoMorphism: Type :=
      { preserves: ∀ (u: σ), Preservation (A_ops u) (B_ops u)
      ; homo_source_algebra: Algebra σ A
      ; homo_target_algebra: Algebra σ B }.

  End with_f.
  End homo.

  Global Instance id_homomorphism A
    `{ao: AlgebraOps σ A} `{!Algebra σ A}: HomoMorphism _ _ (λ _, id).
  Proof with try apply _; auto.
   constructor; intros...
   generalize (ao u).
   induction (σ u); simpl...
  Qed.

  Global Instance compose_homomorphisms A B C f g
    {ao: AlgebraOps σ A} {bo: AlgebraOps σ B} {co: AlgebraOps σ C}
    {gh: HomoMorphism A B g} {fh: HomoMorphism B C f}: HomoMorphism A C (λ a, f a ∘ g a).
  Proof with try apply _; auto.
   pose proof (homo_source_algebra _ _ g).
   pose proof (homo_target_algebra _ _ g).
   pose proof (homo_target_algebra _ _ f).
   constructor; intros...
   generalize (ao u) (bo u) (co u) (preserves _ _ g u) (preserves _ _ f u).
   induction (σ u); simpl; intros.
    rewrite <- X3, <- X2. reflexivity.
   apply (IHo _ (o1 (g _ x))). apply X2. apply X3.
  Qed.

  Lemma invert_homomorphism A B f
    {ao: AlgebraOps σ A} {bo: AlgebraOps σ B}
    {fh: HomoMorphism A B f}
    `{inv: ∀ a, Inverse (f a)}:
    (∀ a, Bijective (f a)) →
    HomoMorphism A B f → HomoMorphism B A inv.
  Proof with try assumption.
   intros ? [? ? ?].
   constructor...
   intro.
   generalize (ao u) (bo u) (preserves _ _ f u).
   induction (σ u); simpl.
    intros.
    apply (injective (f t)).
    pose proof (surjective (f t)).
    rewrite X0.
    exact (transport (λ h, h o0 = o0) (X1^) idpath).
    pose proof (surjective (f t)).
    intros. apply IHo. pose (X1 (inv t x)).
    exact (transport (λ h, Preservation A B f (o0 (inv t x)) (o1 (h x))) X0 p).
  Qed.

End contents.
