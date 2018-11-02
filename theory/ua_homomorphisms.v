Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.universal_algebra
  HoTT.Basics.Equivalences.

Section contents.
  Variable σ: Signature.

  Notation OpType := (OpType (sorts σ)).

  Section homo.
    Context (A B: sorts σ → Type)
      `{A_ops : AlgebraOps σ A} `{B_ops : AlgebraOps σ B}
      (f : ∀ a, A a → B a).

    Fixpoint Preservation {n : OpType}: op_type A n → op_type B n → Type :=
      match n with
      | ne_list.one d => λ oA oB, f _ oA = oB
      | ne_list.cons x y => λ oA oB, ∀ x, Preservation (oA x) (oB (f _ x))
      end.

    Class HomoMorphism: Type :=
      { preserves: ∀ (u: σ), Preservation (A_ops u) (B_ops u)
      ; homomorphism_domain: Algebra σ A
      ; homomorphism_codomain: Algebra σ B }.
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
    {gh: HomoMorphism A B g} {fh: HomoMorphism B C f}
    : HomoMorphism A C (λ a, f a ∘ g a).
  Proof with try apply _; auto.
   pose proof (homomorphism_domain _ _ g).
   pose proof (homomorphism_codomain _ _ g).
   pose proof (homomorphism_codomain _ _ f).
   constructor; intros...
   generalize (ao u) (bo u) (co u) (preserves _ _ g u) (preserves _ _ f u).
   induction (σ u); simpl; intros.
    rewrite <- X3, <- X2. reflexivity.
   apply (IHo _ (o1 (g _ x))). apply X2. apply X3.
  Qed.

  Lemma invert_homomorphism A B f
    {ao: AlgebraOps σ A} {bo: AlgebraOps σ B}
    `{∀ a, IsEquiv (f a)} {h : HomoMorphism A B f}
    : HomoMorphism B A (λ a, (f a)^-1).
  Proof.
   constructor; try (destruct h; assumption).
   intro.
   generalize (ao u) (bo u) (preserves _ _ f u).
   intros.
   induction (σ u); simpl.
    intros.
    rewrite <- X.
    apply (eissect (f t)).
    pose proof (eisretr (f t)).
    intros. apply IHo1.
    exact (transport (λ y, Preservation A B f _ (o0 y)) (X0 x) (X (_^-1 x))).
  Qed.
End contents.
