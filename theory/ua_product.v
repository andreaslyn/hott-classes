Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_algebra
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.theory.ua_homomorphism
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.Types.Sigma.

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
    := op_prodalgebra (σ u) (λ (i:I), u ^^ A i).

  Definition ProdAlgebra : Algebra σ
    := BuildAlgebra carriers_prodalgebra ops_prodalgebra.
End prodalgebra.

Section hom_projection_prodalgebra.
  Context `{Funext} {σ : Signature} {I : Type} (A : I → Algebra σ).

  Definition def_projection_prodalgebra (i:I) (s : sort σ) (c : ProdAlgebra A s)
    : A i s
    := c i.

  Lemma oppreserving_projection_prodalgebra {w : symboltype σ} (i : I)
    (v : ∀ i : I, Operation (A i) w) (ao : Operation (A i) w) (P : v i = ao)
    : OpPreserving (def_projection_prodalgebra i) (op_prodalgebra A w v) ao.
  Proof.
    induction w.
    - exact P.
    - intro p. apply (IHw (λ i, v i (p i)) (ao (p i))). exact (apD10 P (p i)).
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

Section ump_prodalgebra.
  Context
    `{Funext} {σ : Signature} {I : Type} (A : I → Algebra σ) (X : Algebra σ).

  Lemma hom_ump_prodalgebra_factoring
    : Homomorphism X (ProdAlgebra A) → ∀ (i:I), Homomorphism X (A i).
  Proof.
    intros f i.
    exact (BuildHomomorphism (λ s, hom_projection_prodalgebra A i s ∘ f s)).
  Defined.

  Definition def_ump_prodalgebra_mapin (f : ∀ (i:I), Homomorphism X (A i))
    : ∀ (s : sort σ) , X s → ProdAlgebra A s
    := λ (s : sort σ) (x : X s) (i : I), f i s x.

  Lemma oppreserving_ump_prodalgebra_mapin {w : symboltype σ}
    (f : ∀ (i:I), Homomorphism X (A i))
    (xo : Operation X w) (ao : ∀ (i:I), Operation (A i) w)
    (P : ∀ (i:I), OpPreserving (f i) xo (ao i))
    : OpPreserving (def_ump_prodalgebra_mapin f) xo
        (op_prodalgebra A w (λ i : I, ao i)).
  Proof.
    induction w.
    - funext i. apply P.
    - intro x. apply IHw. intro i. apply P.
  Qed.

  Global Instance ishomomorphism_ump_prodalgebra_mapin
    (f : ∀ (i:I), Homomorphism X (A i))
    : IsHomomorphism (def_ump_prodalgebra_mapin f).
  Proof.
    intro u. apply oppreserving_ump_prodalgebra_mapin. intro i. apply f.
  Qed.

  Definition hom_ump_prodalgebra_mapin (f : ∀ (i:I), Homomorphism X (A i))
    : Homomorphism X (ProdAlgebra A)
    := BuildHomomorphism (def_ump_prodalgebra_mapin f).

 Lemma ump_prodalgebra
   : Homomorphism X (ProdAlgebra A) <~> ∀ (i:I), Homomorphism X (A i).
  Proof.
    apply (equiv_adjointify
            hom_ump_prodalgebra_factoring hom_ump_prodalgebra_mapin).
    - intro f. funext i. by apply path_sigma_hprop.
    - intro f. by apply path_sigma_hprop.
  Defined.

End ump_prodalgebra.
