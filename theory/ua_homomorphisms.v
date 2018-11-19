Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.universal_algebra
  HoTT.Basics.Equivalences
  HoTT.Types.Forall.

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

    Global Instance Preservation_hprop `{Funext}
      {AA : Algebra σ A} {BB : Algebra σ B}
      {n : OpType} (a : op_type A n) (b : op_type B n)
      : IsHProp (Preservation a b).
    Proof. intros. induction n; apply _. Defined.

    Class HomoMorphism {dom : Algebra σ A} {cod : Algebra σ B} : Type :=
      preserves: ∀ (u: σ), Preservation (A_ops u) (B_ops u).

    Global Instance HomoMorphism_hprop `{Funext}
        {AA : Algebra σ A} {BB : Algebra σ B} : IsHProp HomoMorphism.
    Proof. intros. apply trunc_forall. Defined.
  End homo.

  Global Instance id_homomorphism A
    `{ao: AlgebraOps σ A} `{!Algebra σ A}: HomoMorphism _ _ (λ _, id).
  Proof with try apply _; auto.
   intros u.
   generalize (ao u).
   induction (σ u); simpl...
  Qed.

  Global Instance compose_homomorphisms A B C f g
    {ao: AlgebraOps σ A} {bo: AlgebraOps σ B} {co: AlgebraOps σ C}
    {AA: Algebra σ A} {BB: Algebra σ B} {CC: Algebra σ C}
    {gh: HomoMorphism A B g} {fh: HomoMorphism B C f}
    : HomoMorphism A C (λ a, f a ∘ g a).
  Proof with try apply _; auto.
   intros u.
   generalize (ao u) (bo u) (co u) (preserves _ _ g u) (preserves _ _ f u).
   induction (σ u); simpl; intros.
    rewrite <- X0, <- X. reflexivity.
   apply (IHo _ (o1 (g _ x))). apply X. apply X0.
  Qed.

  Lemma invert_homomorphism A B f
    {ao: AlgebraOps σ A} {bo: AlgebraOps σ B}
    {AA: Algebra σ A} {BB: Algebra σ B}
    `{∀ a, IsEquiv (f a)} {h : HomoMorphism A B f}
    : HomoMorphism B A (λ a, (f a)^-1).
  Proof.
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
