Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.theory.ua_homomorphism
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Types.Sigma
  HoTT.Basics.Overture.

Import algebra_notations.

Section closed_subalgebra.
  Context
    {σ : Signature}
    {A : Algebra σ}
    (P : ∀ (s : sort σ), A s → Type)
    `{!∀ (s : sort σ) (x : A s), IsHProp (P s x)}.

  Fixpoint op_closed_subalgebra {w : symboltype σ} : Operation A w → Type :=
    match w with
    | [:x] => P x
    | _ ::: _ => λ d, ∀ z, P _ z → op_closed_subalgebra (d z)
    end.

  Global Instance hprop_op_closed_subalg `{Funext} (w : symboltype σ)
      (bo : Operation A w) : IsHProp (op_closed_subalgebra bo).
  Proof. induction w; apply _. Defined.

  Class ClosedSubalgebra : Type :=
    closed_subalgebra : ∀ (u : symbol σ), op_closed_subalgebra (u^^A).
End closed_subalgebra.

Section subalgebra.
  Context
    {σ : Signature} {A : Algebra σ}
    (P : ∀ (s : sort σ), A s → Type) `{!∀ s x, IsHProp (P s x)}
    `{!ClosedSubalgebra P}.

  Definition carriers_subalgebra : Carriers σ := λ (s : sort σ), {x | P s x}.

  Fixpoint op_subalgebra {w : symboltype σ}
    : ∀ (a : Operation A w),
      op_closed_subalgebra P a → Operation carriers_subalgebra w
    := match w with
       | [:_] => λ u c, (u; c)
       | _ ::: _ => λ u c x, op_subalgebra (u (pr1 x)) (c (pr1 x) (pr2 x))
       end.

  Definition ops_subalgebra (u : symbol σ)
    : Operation carriers_subalgebra (σ u)
    := op_subalgebra (u^^A) (closed_subalgebra P u).
  
  Definition Subalgebra : Algebra σ
    := BuildAlgebra carriers_subalgebra ops_subalgebra.

  Definition def_inclusion_subalgebra (s : sort σ) : Subalgebra s → A s := pr1.

  Lemma oppreserving_inclusion_subalgebra {w : symboltype σ}
    (ao : Operation A w) (co : op_closed_subalgebra P ao)
    : OpPreserving def_inclusion_subalgebra (op_subalgebra ao co) ao.
  Proof.
    induction w.
    - reflexivity.
    - intros x. apply IHw.
  Qed.

  Global Instance ishomomorphism_inclusion_subalgebra
    : IsHomomorphism def_inclusion_subalgebra.
  Proof.
    intro u. apply oppreserving_inclusion_subalgebra.
  Qed.

  Definition hom_inclusion_subalgebra : Homomorphism Subalgebra A
    := BuildHomomorphism def_inclusion_subalgebra.

  Global Instance injection_def_inclusion_subalgebra
    : ∀ (s : sort σ), Injective (def_inclusion_subalgebra s).
  Proof.
    intros s x y p. by apply path_sigma_hprop.
  Qed.
End subalgebra.
