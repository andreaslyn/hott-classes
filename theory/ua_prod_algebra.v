Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Prod
  HoTTClasses.interfaces.ua_algebra
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.theory.ua_homomorphism.

Import algebra_notations ne_list.notations.

Section prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I → Algebra σ).

  Definition carriers_prod_algebra : Carriers σ
    := λ (s : Sort σ), ∀ (i:I), A i s.

  Fixpoint op_prod_algebra (w : SymbolType σ)
      : (∀ i, Operation (A i) w) →
        Operation carriers_prod_algebra w :=
    match w return (∀ i, Operation (A i) w) →
                   Operation carriers_prod_algebra w
    with
    | [:_:] => idmap
    | _ ::: g => λ f p, op_prod_algebra g (λ i, f i (p i))
    end.

  Definition ops_prod_algebra (u : Symbol σ)
    : Operation carriers_prod_algebra (σ u)
    := op_prod_algebra (σ u) (λ (i:I), u ^^ A i).

  Definition ProdAlgebra : Algebra σ
    := BuildAlgebra carriers_prod_algebra ops_prod_algebra.
End prod_algebra.

Section hom_projection_prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I → Algebra σ).

  Definition def_projection_prod_algebra (i:I) (s : Sort σ)
      (c : ProdAlgebra I A s)
    : A i s
    := c i.

  Lemma oppreserving_projection_prod_algebra {w : SymbolType σ}
    (i : I) (v : ∀ i : I, Operation (A i) w) (α : Operation (A i) w)
    (P : v i = α)
    : OpPreserving (def_projection_prod_algebra i)
        (op_prod_algebra I A w v) α.
  Proof.
    induction w.
    - exact P.
    - intro p. apply (IHw (λ i, v i (p i)) (α (p i))). f_ap.
  Qed.

  Global Instance is_homomorphism_projection_prod_algebra (i:I)
    : IsHomomorphism (def_projection_prod_algebra i).
  Proof.
    intro u.
    by apply oppreserving_projection_prod_algebra.
  Qed.

  Definition hom_projection_prod_algebra (i : I)
    : Homomorphism (ProdAlgebra I A) (A i)
    := BuildHomomorphism (def_projection_prod_algebra i).
End hom_projection_prod_algebra.

Section ump_prod_algebra.
  Context
    `{Funext}
    {σ : Signature}
    (I : Type)
    (A : I → Algebra σ)
    (C : Algebra σ).

  Definition hom_ump_prod_algebra_factoring
    (f : Homomorphism C (ProdAlgebra I A)) (i:I)
    : Homomorphism C (A i)
    := BuildHomomorphism (λ s, hom_projection_prod_algebra I A i s ∘ f s).

  Definition def_ump_prod_algebra_mapin (f : ∀ i, Homomorphism C (A i))
    : ∀ (s : Sort σ) , C s → ProdAlgebra I A s
    := λ (s : Sort σ) (x : C s) (i : I), f i s x.

  Lemma oppreserving_ump_prod_algebra_mapin {w : SymbolType σ}
    (f : ∀ (i:I), Homomorphism C (A i))
    (α : ∀ (i:I), Operation (A i) w) (β : Operation C w)
    (P : ∀ (i:I), OpPreserving (f i) β (α i))
    : OpPreserving (def_ump_prod_algebra_mapin f) β
        (op_prod_algebra I A w (λ (i:I), α i)).
  Proof.
    induction w.
    - funext i. apply P.
    - intro x. apply IHw. intro i. apply P.
  Qed.

  Global Instance is_homomorphism_ump_prod_algebra_mapin
    (f : ∀ (i:I), Homomorphism C (A i))
    : IsHomomorphism (def_ump_prod_algebra_mapin f).
  Proof.
    intro u.
    apply oppreserving_ump_prod_algebra_mapin.
    intro i.
    apply f.
  Qed.

  Definition hom_ump_prod_algebra_mapin (f : ∀ i, Homomorphism C (A i))
    : Homomorphism C (ProdAlgebra I A)
    := BuildHomomorphism (def_ump_prod_algebra_mapin f).

 Lemma ump_prod_algebra
   : Homomorphism C (ProdAlgebra I A) <~> ∀ (i:I), Homomorphism C (A i).
  Proof.
    apply (equiv_adjointify
            hom_ump_prod_algebra_factoring hom_ump_prod_algebra_mapin).
    - intro f. funext i. by apply path_homomorphism.
    - intro f. by apply path_homomorphism.
  Defined.
End ump_prod_algebra.

Section bin_prod_algebra.
  Context `{Funext} {σ : Signature} (A B : Algebra σ).

  Definition bin_prod_algebras (b:Bool) : Algebra σ
    := if b then B else A.

  Definition BinProdAlgebra : Algebra σ :=
    ProdAlgebra Bool bin_prod_algebras.

  Definition fst_prod_algebra : Homomorphism BinProdAlgebra A
    := hom_projection_prod_algebra Bool bin_prod_algebras false.

  Definition snd_prod_algebra : Homomorphism BinProdAlgebra B
    := hom_projection_prod_algebra Bool bin_prod_algebras true.
End bin_prod_algebra.

Module prod_algebra_notations.

  Global Notation "A × B" := (BinProdAlgebra A B)
                             (at level 40, left associativity)
                             : Algebra_scope.

End prod_algebra_notations.

Import prod_algebra_notations.

Section ump_bin_prod_algebra.
  Context `{Funext} {σ : Signature} (A B C : Algebra σ).

 Lemma ump_bin_prod_algebra
   : Homomorphism C (A × B) <~> Homomorphism C A * Homomorphism C B.
  Proof.
    exact (equiv_compose
            (equiv_bool_forall_prod
              (λ (b:Bool), Homomorphism C (bin_prod_algebras A B b)))
            (ump_prod_algebra Bool (bin_prod_algebras A B) C)).
  Defined.
End ump_bin_prod_algebra.
