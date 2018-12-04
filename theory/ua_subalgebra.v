Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.theory.ua_homomorphism
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Types.Sigma
  HoTT.Basics.Overture.

Import algebra_notations.

Section closed_subalg.
  Context
    {σ : Signature} {A : Algebra σ}
    (P : ∀ (s : sort σ), A s → Type) `{!∀ s x, IsHProp (P s x)}.

  Fixpoint op_closed_subalg {w : symboltype σ} : op_type A w → Type :=
    match w with
    | [:x:] => P x
    | _ ::: _ => λ d, ∀ z, P _ z → op_closed_subalg (d z)
    end.

  Global Instance hprop_op_closed_subalg `{Funext} (w : symboltype σ)
      (bo : op_type A w) : IsHProp (op_closed_subalg bo).
  Proof. induction w; apply _. Defined.

  Class ClosedSubalg : Type :=
    closed_subalg : ∀ (u : symbol σ), op_closed_subalg u^^A.
End closed_subalg.

Section subalg.
  Context
    {σ : Signature} {A : Algebra σ}
    (P : ∀ (s : sort σ), A s → Type) `{!∀ s x, IsHProp (P s x)}
    `{!ClosedSubalg P}.

  Definition carriers_subalg : Carriers σ := λ (s : sort σ), {x | P s x}.

  Fixpoint op_subalg {w : symboltype σ}
    : ∀ (a : op_type A w), op_closed_subalg P a → op_type carriers_subalg w
    := match w with
       | [:_:] => λ u c, (u; c)
       | _ ::: _ => λ u c x, op_subalg (u (pr1 x)) (c (pr1 x) (pr2 x))
       end.

  Definition opfamily_subalg (u : symbol σ) : op_type carriers_subalg (σ u)
    := op_subalg u^^A (closed_subalg P u).
  
  Definition subalg : Algebra σ
    := BuildAlgebra carriers_subalg opfamily_subalg.

  Definition fn_inclusion_subalg (s : sort σ) : subalg s → A s := pr1.

  Lemma oppreserving_inclusion_subalg {w : symboltype σ}
    (ao : op_type A w) (co : op_closed_subalg P ao)
    : OpPreserving fn_inclusion_subalg (op_subalg ao co) ao.
  Proof.
    induction w.
    - reflexivity.
    - intros x. apply IHw.
  Qed.

  Global Instance ishomomorphism_inclusion_subalg
    : IsHomomorphism fn_inclusion_subalg.
  Proof.
    intro u. apply oppreserving_inclusion_subalg.
  Qed.

  Definition hom_inclusion_subalg : Homomorphism subalg A
    := BuildHomomorphism fn_inclusion_subalg.

  Global Instance injection_fn_inclusion_subalg
    : ∀ (s : sort σ), Injective (fn_inclusion_subalg s).
  Proof.
    intros s x y p. by apply path_sigma_hprop.
  Qed.
End subalg.
