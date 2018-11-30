Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_basic
  HoTTClasses.implementations.ne_list
  HoTTClasses.theory.ua_homomorphisms
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Types.Sigma
  HoTT.Basics.Overture.

Import nel.notations algebra_notations.

Section closed_subalg.
  Context
    {σ : Signature} {A : Algebra σ}
    (P : ∀ (s : sigsort σ), A s → Type) `{!∀ s x, IsHProp (P s x)}.

  Fixpoint op_closed_subalg {w : opsym_type σ} : op_type A w → Type :=
    match w with
    | [:x:] => P x
    | _ ::: _ => λ d, ∀ z, P _ z → op_closed_subalg (d z)
    end.

  Global Instance hprop_op_closed_subalg `{Funext} (w : opsym_type σ)
      (bo : op_type A w) : IsHProp (op_closed_subalg bo).
  Proof. induction w; apply _. Defined.

  Class ClosedSubalg : Type :=
    closed_subalg : ∀ (u : sigsym σ), op_closed_subalg (u^^A).
End closed_subalg.

Section subalg.
  Context
    {σ : Signature} {A : Algebra σ}
    (P : ∀ (s : sigsort σ), A s → Type) `{!∀ s x, IsHProp (P s x)}
    `{!ClosedSubalg P}.

  Definition carriers_subalg : Carriers σ := λ (s : sigsort σ), {x | P s x}.

  Fixpoint op_subalg {w : opsym_type σ}
    : ∀ (a : op_type A w), op_closed_subalg P a → op_type carriers_subalg w
    := match w with
       | [:_:] => λ u c, (u; c)
       | _ ::: _ => λ u c x, op_subalg (u (pr1 x)) (c (pr1 x) (pr2 x))
       end.

  Definition opfamily_subalg (u : sigsym σ) : op_type carriers_subalg (σ u)
    := op_subalg (u^^A) (closed_subalg P u).
  
  Definition subalg : Algebra σ
    := BuildAlgebra carriers_subalg opfamily_subalg.

  Definition fn_inclusion_subalg (s : sigsort σ) : subalg s → A s := pr1.

  Lemma oppreserving_inclusion_subalg {w : opsym_type σ}
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

  Global Instance setinjection_fn_inclusion_subalg
    : ∀ (s : sigsort σ), Injective (fn_inclusion_subalg s).
  Proof.
    intros s x y p. by apply path_sigma_hprop.
  Qed.
End subalg.
