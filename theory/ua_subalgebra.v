Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.theory.ua_homomorphism
  HoTT.Types.Sigma
  HoTT.Basics.Overture.

Import algebra_notations ne_list.notations.

Section closed_subalgebra.
  Context
    {σ : Signature}
    (A : Algebra σ)
    (P : ∀ (s : Sort σ), A s → Type)
    `{!∀ (s : Sort σ) (x : A s), IsHProp (P s x)}.

  Fixpoint ClosedUnderOp {w : SymbolType σ} : Operation A w → Type :=
    match w with
    | [:x:] => P x
    | s ::: w' => λ (f : A s → Operation A w'),
                    ∀ (x : A s), P s x → ClosedUnderOp (f x)
    end.

  Global Instance hprop_op_closed_subalgebra `{Funext} (w : SymbolType σ)
      (f : Operation A w) : IsHProp (ClosedUnderOp f).
  Proof. induction w; exact _. Defined.

  Class IsClosedUnderOps : Type :=
    closed_subalgebra : ∀ (u : Symbol σ), ClosedUnderOp (u^^A).
End closed_subalgebra.

Section subalgebra.
  Context
    {σ : Signature}
    (A : Algebra σ)
    (P : ∀ (s : Sort σ), A s → Type)
    `{!∀ s (x : A s), IsHProp (P s x)}
    `{!IsClosedUnderOps A P}.

  Definition carriers_subalgebra : Carriers σ := λ (s : Sort σ), {x | P s x}.

  Fixpoint op_subalgebra {w : SymbolType σ}
    : ∀ (f : Operation A w),
      ClosedUnderOp A P f → Operation carriers_subalgebra w
    := match w with
       | [:_:] => λ u c, (u; c)
       | _ ::: _ => λ u c x, op_subalgebra (u (pr1 x)) (c (pr1 x) (pr2 x))
       end.

  Definition ops_subalgebra (u : Symbol σ)
    : Operation carriers_subalgebra (σ u)
    := op_subalgebra (u^^A) (closed_subalgebra A P u).
  
  Definition Subalgebra : Algebra σ
    := BuildAlgebra carriers_subalgebra ops_subalgebra.
End subalgebra.

Module subalgebra_notations.
  Notation "A & P" := (Subalgebra A P) (at level 50, left associativity)
    : Algebra_scope.
End subalgebra_notations.

Import subalgebra_notations.

Section hom_inclusion_subalgebra.
  Context
    {σ : Signature}
    (A : Algebra σ)
    (P : ∀ (s : Sort σ), A s → Type)
    `{!∀ s (x : A s), IsHProp (P s x)}
    `{!IsClosedUnderOps A P}.

  Definition def_inclusion_subalgebra (s : Sort σ) : (A&P) s → A s := pr1.

  Lemma oppreserving_inclusion_subalgebra {w : SymbolType σ}
    (f : Operation A w) (C : ClosedUnderOp A P f)
    : OpPreserving def_inclusion_subalgebra (op_subalgebra A P f C) f.
  Proof.
    induction w.
    - reflexivity.
    - intros x. apply IHw.
  Qed.

  Global Instance is_homomorphism_inclusion_subalgebra
    : IsHomomorphism def_inclusion_subalgebra.
  Proof.
    intro u. apply oppreserving_inclusion_subalgebra.
  Qed.

  Definition hom_inclusion_subalgebra : Homomorphism (A&P) A
    := BuildHomomorphism def_inclusion_subalgebra.

  Global Instance injection_inclusion_subalgebra
    : ∀ (s : Sort σ), Injective (hom_inclusion_subalgebra s).
  Proof.
    intros s x y p. by apply path_sigma_hprop.
  Qed.

  Lemma surjection_inclusion_subalgebra (total : ∀ s x, P s x)
    : ∀ (s : Sort σ), IsSurjection (hom_inclusion_subalgebra s).
  Proof.
    intros s.
    apply BuildIsSurjection.
    intro y.
    apply tr.
    by exists (y; total s y).
  Qed.

  Lemma is_isomorphism_inclusion_subalgebra (total : ∀ s x, P s x)
    : IsIsomorphism hom_inclusion_subalgebra.
  Proof.
    constructor.
    - exact _.
    - by apply surjection_inclusion_subalgebra.
  Defined.

  Lemma path_ap_operation_inclusion_subalgebra
    {w : SymbolType σ} a (f : Operation A w) C
    : ap_operation f (map_family_prod hom_inclusion_subalgebra a)
      = hom_inclusion_subalgebra (cod_symboltype w)
          (ap_operation (op_subalgebra A P f C) a).
  Proof.
    induction w.
    - reflexivity.
    - apply IHw.
  Defined.
End hom_inclusion_subalgebra.
