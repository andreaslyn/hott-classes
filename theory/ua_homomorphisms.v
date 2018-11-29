Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_basic
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.HSet
  HoTT.Types.Universe
  HoTT.Basics.PathGroupoids
  HoTT.Tactics.

Import algebra_notations.
Import ne_list.notations.

(* TODO Put this next to Injective and rename Injective. *)
Class IsSetSurjection {A B : Type} (f : A → B) : Type :=
  is_set_surjection : ∀ (y:B), hfiber f y.

Notation hom_type := (λ (A B : Algebra _), ∀ (s : sign_sort _), A s → B s).

Section ishomomorphism.
  Context {σ : Signature} {A B : Algebra σ} (f : hom_type A B).

  Fixpoint op_preservation {n : op_symbol_type σ}
    : op_type A n → op_type B n → Type
    := match n with
       | ne_list.one d => λ oA oB, f _ oA = oB
       | ne_list.cons x y => λ oA oB, ∀ x, op_preservation (oA x) (oB (f _ x))
       end.

  Global Instance hprop_op_preservation {Fu : Funext} {n : op_symbol_type σ}
    (a : op_type A n) (b : op_type B n)
    : IsHProp (op_preservation a b).
  Proof.
    intros. induction n; apply _.
  Defined.

  Class IsHomomorphism : Type :=
    hom_preserves : ∀ (u : sign_symbol σ), op_preservation (u^^A) (u^^B).

  Global Instance hprop_ishomomorphism {Fu : Funext} : IsHProp IsHomomorphism.
  Proof.
    intros. apply trunc_forall.
  Defined.

  Class IsIsomorphism `{Ho : IsHomomorphism} : Type :=
    { setinjection_isomorphism : ∀ (s : sign_sort σ), Injective (f s)
    ; setsurjection_isomorphism : ∀ (s : sign_sort σ), IsSetSurjection (f s) }.

  Global Existing Instance setinjection_isomorphism.
  Global Existing Instance setsurjection_isomorphism.
End ishomomorphism.

Record Homomorphism {σ} (A B : Algebra σ) : Type := BuildHomomorphism
  { hom_map : hom_type A B
  ; ishomomorphism_hom : IsHomomorphism hom_map }.

Global Coercion hom_map : Homomorphism >-> Funclass.
Global Existing Instance ishomomorphism_hom.

Arguments BuildHomomorphism {σ} {A} {B} hom_map {ishomomorphism_hom}.

Global Instance isequiv_forgetful_isomorphism {σ} {A B : Algebra σ}
    (f : Homomorphism A B) {Is : IsIsomorphism f}
    : ∀ s, IsEquiv (f s).
Proof.
  intro s. apply isequiv_surj_emb.
  - apply BuildIsSurjection. intro y. apply tr. apply Is.
  - apply isembedding_isinj_hset. apply Is.
Defined.

Definition equiv_forgetful_isomorphism {σ} {A B : Algebra σ}
    (f : Homomorphism A B) {Is : IsIsomorphism f}
    : ∀ s, A s <~> B s.
Proof.
  intro s. rapply (BuildEquiv _ _ (f s)).
Defined.

Global Instance ishomomorphism_hom_id {σ} (A : Algebra σ)
  : IsHomomorphism (λ _, idmap).
Proof.
 intro u. generalize (u^^A). intro w. induction (σ u).
 - reflexivity.
 - now intro x.
Qed.

Global Instance isisomorphism_hom_id {σ} (A : Algebra σ)
  : IsIsomorphism (λ _, idmap).
Proof.
  constructor; intro s.
  - intros x y. exact idmap.
  - intro y. exact (y; idpath).
Qed.

Definition hom_id {σ} {A : Algebra σ} : Homomorphism A A
  := BuildHomomorphism (λ _, idmap).

Global Instance ishomomorphism_hom_compose {σ} {A B C : Algebra σ}
  (g : Homomorphism B C) (f : Homomorphism A B)
  : IsHomomorphism (λ s, g s ∘ f s).
Proof.
 unfold Compose.
 intro u.
 generalize (hom_preserves g u) (hom_preserves f u).
 generalize (u^^A) (u^^B) (u^^C).
 induction (σ u); simpl; intros x y z G F.
 - now rewrite F, G.
 - intro a. now apply (IHl _ (y (f _ a))).
Qed.

Definition hom_compose {σ} {A B C : Algebra σ}
    (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
  := BuildHomomorphism (λ s, g s ∘ f s).

Global Instance ishomomorphism_hom_inv {σ} (A B : Algebra σ)
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : IsHomomorphism (λ s, (f s)^-1).
Proof.
 intro.
 generalize (u^^A) (u^^B) (hom_preserves f u).
 induction (σ u); intros a b P.
 - rewrite <- P. apply (eissect (f t)).
 - intro. apply IHl.
   exact (
    transport (λ y, op_preservation f _ (b y)) (eisretr (f t) x) (P (_^-1 x))).
Qed.

Global Instance isisomorphism_hom_inv {σ} (A B : Algebra σ)
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : IsIsomorphism (λ s, (f s)^-1).
Proof.
  constructor.
  - intros s x y p.
    now rewrite <- (eisretr (f s) x), <- (eisretr (f s) y), p.
  - intros s y. exists (f s y). apply (eissect (f s) y).
Qed.

Definition hom_inv {σ} {A B : Algebra σ} (f : Homomorphism A B)
    `{!IsIsomorphism f}
    : Homomorphism B A
  := BuildHomomorphism (λ s, (f s)^-1).

Definition path_equiv_carriers `{Univalence} {σ} {A B : Algebra σ}
  (f : ∀ (s : sign_sort σ), A s <~> B s)
  : carriers A = carriers B
  := path_forall A B (λ s : sign_sort σ, path_universe (f s)).

Lemma path_transport_carriers_isomorphism' `{Univalence} {σ} {A B : Algebra σ}
  {w : op_symbol_type σ} (f : ∀ (s : sign_sort σ), A s <~> B s)
  (ao : op_type A w) (bo : op_type B w) (P : op_preservation f ao bo)
  : transport (λ s : σ.(sign_sort) → Type, op_type s w)
      (path_equiv_carriers f) ao = bo.
Proof.
  unfold path_equiv_carriers.
  induction w; simpl in *.
  transport_path_forall_hammer.
  rewrite <- P.
  rewrite transport_idmap_path_universe.
  reflexivity.
  funext x.
  pose (P ((f t)^-1 x)) as P'.
  rewrite (eisretr (f t)) in P'.
  pose (IHw (ao ((f t)^-1 x)) (bo x) P') as IHl'.
  transport_path_forall_hammer.
  rewrite transport_forall_constant.
  rewrite transport_forall.
  rewrite transport_const.
  rewrite (transport_path_universe_V (f t)).
  destruct (path_universe (f t)).
  apply IHl'.
Qed.

Lemma path_transport_carriers_isomorphism `{Univalence} {σ} {A B : Algebra σ}
  (f : Homomorphism A B) `{!IsIsomorphism f} (u : sign_symbol σ):
  transport (λ s : sign_sort σ → Type, op_type s (σ u))
    (path_equiv_carriers (equiv_forgetful_isomorphism f)) (u ^^ A)
  = u ^^ B.
Proof.
  apply path_transport_carriers_isomorphism'. apply (hom_preserves f).
Defined.

Theorem path_isomorphism `{Univalence} {σ} {A B : Algebra σ}
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : A = B.
Proof.
  apply path_pair_algebra_algebra.
  exists (path_equiv_carriers (equiv_forgetful_isomorphism f)).
  funext u.
  refine (transport (λ x : op_type B (σ u), x = u ^^ B)
            (transport_forall_constant _ _ u)^
            (path_transport_carriers_isomorphism f u)).
Defined.
