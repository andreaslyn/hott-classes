Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_basic
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.HSet.

Class Surjective {A B : Type} (f : A → B) : Type :=
  surjective : ∀ (y:B), hfiber f y.

Notation hom_type := (λ (A B : Algebra _), ∀ (s : sig_sort _), A s → B s).

Section ishomomorphism.
  Context {σ: Signature} {A B : Algebra σ} (f : hom_type A B).

  Fixpoint Preservation {n : sig_fn_type σ}: op_type A n → op_type B n → Type :=
    match n with
    | ne_list.one d => λ oA oB, f _ oA = oB
    | ne_list.cons x y => λ oA oB, ∀ x, Preservation (oA x) (oB (f _ x))
    end.

  Global Instance Preservation_hprop {Fu : Funext} {n : sig_fn_type σ}
    (a : op_type A n) (b : op_type B n)
    : IsHProp (Preservation a b).
  Proof. intros. induction n; apply _. Defined.

  Class IsHomomorphism : Type :=
    hom_preserves : ∀ (u: σ), Preservation (algebra_op A u) (algebra_op B u).

  Global Instance HomoMorphism_hprop {Fu : Funext} : IsHProp IsHomomorphism.
  Proof. intros. apply trunc_forall. Defined.

  Class IsIsomorphism `{Ho : IsHomomorphism} : Type :=
    { iso_isembedding :> ∀ (s : sig_sort σ), Injective (f s)
    ; iso_issuejection :> ∀ (s : sig_sort σ), Surjective (f s) }.

End ishomomorphism.

Record Homomorphism {σ} (A B : Algebra σ) : Type := BuildHomomorphism
  { hom_map :> hom_type A B
  ; hom_ishomomorphism : IsHomomorphism hom_map }.

Global Existing Instance hom_ishomomorphism.

Arguments BuildHomomorphism {σ} {A} {B} hom_map {hom_ishomomorphism}.

Record Isomorphism {σ} (A B : Algebra σ) : Type := BuildIsomorphism'
  { iso_homomorphism :> Homomorphism A B
  ; iso_isisomorphism : IsIsomorphism iso_homomorphism }.

Global Existing Instance iso_isisomorphism.

Arguments BuildIsomorphism' {σ} {A} {B} iso_homomorphism {iso_isisomorphism}.

Definition BuildIsomorphism {σ} {A B : Algebra σ} (f : hom_type A B)
    `{!IsHomomorphism f} `{!IsIsomorphism f}
    : Isomorphism A B
  := BuildIsomorphism' (BuildHomomorphism f).

Global Instance isomorphism_isembedding {σ} {A B : Algebra σ}
    (f : Isomorphism A B)
    : ∀ s, IsEmbedding (f s).
Proof. intro s. apply isembedding_isinj_hset. apply f. Defined.

Global Instance isomorphism_issurjection {σ} {A B : Algebra σ}
    (f : Isomorphism A B)
    : ∀ s, IsSurjection (f s).
Proof. intro s. apply BuildIsSurjection. intro y. apply tr. apply f. Defined.

Global Instance isomorphism_isequiv {σ} {A B : Algebra σ}
    (f : Isomorphism A B)
    : ∀ s, IsEquiv (f s).
Proof. intro s. apply isequiv_surj_emb; apply _. Defined.

Definition isomorphism_equiv {σ} (A B : Algebra σ) (f : Isomorphism A B)
    (s : sig_sort σ) : algebra_carriers A s <~> algebra_carriers B s
  := BuildEquiv (A s) (B s) (f s) (isomorphism_isequiv f s).

Global Instance hom_id_ishomomorphism {σ} (A : Algebra σ)
  : IsHomomorphism (λ _, idmap).
Proof.
 intro u. generalize (algebra_op _ u). intro w. induction (σ u).
 - reflexivity.
 - now intro x.
Qed.

Global Instance hom_id_isisomorphism {σ} (A : Algebra σ)
  : IsIsomorphism (λ _, idmap).
Proof.
  constructor; intro s.
  - intros x y. exact idmap.
  - intro y. exact (y; idpath).
Qed.

Definition hom_id {σ : Signature} {A : Algebra σ} : Isomorphism A A
  := BuildIsomorphism (λ _, idmap).

Global Instance hom_compose_ishomomorphism {σ : Signature} {A B C : Algebra σ}
  (g : Homomorphism B C) (f : Homomorphism A B)
  : IsHomomorphism (λ s, g s ∘ f s).
Proof.
 unfold Compose.
 intro u.
 generalize (hom_preserves g u) (hom_preserves f u).
 generalize (algebra_op A u) (algebra_op B u) (algebra_op C u).
 induction (σ u); simpl; intros x y z G F.
 - now rewrite F, G.
 - intro a. now apply (IHf0 _ (y (f _ a))).
Qed.

Definition hom_compose {σ : Signature} {A B C : Algebra σ}
    (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
  := BuildHomomorphism (λ s, g s ∘ f s).

Global Instance iso_inverse_ishomomorphism {σ} (A B : Algebra σ)
  (f : Isomorphism A B)
  : IsHomomorphism (λ s, (f s)^-1).
Proof.
 intro.
 generalize (algebra_op A u) (algebra_op B u) (hom_preserves f u).
 induction (σ u); intros a b P.
 - rewrite <- P. apply (eissect (f t)).
 - intro. apply IHf0.
   exact (transport (λ y, Preservation f _ (b y)) (eisretr (f t) x) (P (_^-1 x))).
Qed.

Global Instance iso_inverse_isisomorphism {σ} (A B : Algebra σ)
  (f : Isomorphism A B)
  : IsIsomorphism (λ s, (f s)^-1).
Proof.
  constructor.
  - intros s x y p.
    now rewrite <- (eisretr (f s) x), <- (eisretr (f s) y), p.
  - intros s y. exists (f s y). apply (eissect (f s) y).
Qed.

Definition iso_inverse {σ : Signature} {A B : Algebra σ} (f : Isomorphism A B)
    : Isomorphism B A
  := BuildIsomorphism (λ s, (f s)^-1).
