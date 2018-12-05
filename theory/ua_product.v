Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_algebra
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.theory.ua_homomorphism
  HoTT.Types.Forall
  HoTT.Basics.Overture.

Import algebra_notations.

Section prodalgebra.
  Context `{Funext} {σ : Signature} {I : Type} (A : I → Algebra σ).

  Definition carriers_prodalgebra : Carriers σ
    := λ (s : sort σ), ∀ (i : I), A i s.

  Fixpoint op_prodalgebra (w : symboltype σ)
      : (∀ i, Operation (A i) w) → Operation carriers_prodalgebra w :=
    match w
      return (∀ i, Operation (A i) w) → Operation carriers_prodalgebra w
    with
    | [:_] => idmap
    | _ ::: g => λ f p, op_prodalgebra g (λ i, f i (p i))
    end.

  Definition ops_prodalgebra (u : symbol σ)
    : Operation carriers_prodalgebra (σ u)
    := op_prodalgebra (σ u) (λ i, u^^(A i)).

  Definition ProdAlgebra : Algebra σ
    := BuildAlgebra carriers_prodalgebra ops_prodalgebra.
End prodalgebra.

Section hom_projection_prodalgebra.
  Context `{Funext} {σ : Signature} {I : Type} (A : I → Algebra σ).

  Definition def_projection_prodalgebra (i:I) (s : sort σ) (c : ProdAlgebra A s)
    : A i s
    := c i.

  Lemma oppreserving_projection_prodalgebra {w : symboltype σ} (i : I)
    (sel : ∀ i : I, Operation (A i) w) (ao : Operation (A i) w) (P : sel i = ao)
    : OpPreserving (def_projection_prodalgebra i) (op_prodalgebra A w sel) ao.
  Proof.
    induction w.
    - exact P.
    - intro p.
      apply (IHw (λ i, sel i (p i)) (ao (p i))).
      exact (apD10 P (p i)).
  Qed.

  Global Instance ishomomorphism_projection_prodalgebra (i:I)
    : IsHomomorphism (def_projection_prodalgebra i).
  Proof.
    intro u.
    by apply oppreserving_projection_prodalgebra.
  Qed.

  Definition hom_projection_prodalgebra (i : I)
    : Homomorphism (ProdAlgebra A) (A i)
    := BuildHomomorphism (def_projection_prodalgebra i).
End hom_projection_prodalgebra.

Section prod_property.
  Context
    `{Funext} {σ : Signature} {I : Type}
    (A : I → Algebra σ) (X : Algebra σ).

  Lemma left_right : Homomorphism X (ProdAlgebra A) → ∀ (i:I), Homomorphism X (A i).
  Proof.
    intros f i.
    exact (BuildHomomorphism (λ s, hom_projection_prodalgebra A i s ∘ f s)).
  Defined.

  Definition def_right_left (f : ∀ (i:I), Homomorphism X (A i))
    : ∀ s, X s → ProdAlgebra A s
    := λ s x i, f i s x.

  Global Instance ishomomorphism_right_left (f : ∀ (i:I), Homomorphism X (A i))
    : IsHomomorphism (def_right_left f).
  Proof.
    intro u.
    generalize (λ i, op_preserving (f i) u).
    set (test i := u ^^ A i).
    set (test' u i := u ^^ A i).
    assert (∀ i, test i = test' u i).
    reflexivity.
    assert ((∀ i : I, OpPreserving (f i) (u ^^ X) (u ^^ A i)) =
              (∀ i : I, OpPreserving (f i) (u ^^ X) (test i))).
    reflexivity.
    assert ((λ u0 : symbol σ, op_prodalgebra A (σ u0) (λ i : I, u0 ^^ A i)) =
              (λ u0 : symbol σ, op_prodalgebra A (σ u0) (λ i : I, test' u0 i))).
    reflexivity.
    rewrite X1.
    clear X1.
    unfold ProdAlgebra.
    unfold ops_prodalgebra.
    unfold BuildAlgebra.
    rewrite X2.
    clear X2.
    clearbody test.
    clearbody test'.
    set (xo := u^^X).
    clearbody xo.
    intro P.
    unfold operations.
    simpl.
    assert ((λ i : I, test' u i) = λ i, test i).
    funext i. rewrite X0. reflexivity.
    rewrite X1.
    clear X1.
    clear X0.
    induction (σ u); simpl in *.
    - unfold def_right_left. funext i. apply P.
    - intro x. apply IHn.
      intro i.
      apply P.
  Defined.

  Lemma right_left : (∀ (i:I), Homomorphism X (A i)) → Homomorphism X (ProdAlgebra A).
  Proof.
    intros f.
    refine (BuildHomomorphism (def_right_left f)).
  Defined.

  Lemma : Homomorphism X ProdAlgebra <~> ∀ (i:I), Homomorphism X (A i)

End prod_property.
