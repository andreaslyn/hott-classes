(* FIXME: NEEDS CLEANUP. *)

Require Import
  HoTT.Basics.Equivalences
  HoTT.Basics.PathGroupoids
  HoTT.Types.Forall
  HoTT.Types.Arrow
  HoTT.Types.Universe
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.HSet
  HoTT.Tactics
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.theory.ua_homomorphism.

Import algebra_notations.

Theorem path_isomorphism' `{Univalence} {σ} (A B : Algebra σ)
  : {f : Homomorphism A B | IsIsomorphism f} → A = B.
Proof.
  intros [f F]. apply (path_isomorphism f).
Defined.

Lemma isomorphism_path' {σ} (A B : Algebra σ)
  : A = B → {f : Homomorphism A B | IsIsomorphism f}.
Proof.
  intro p.
  refine (transport (λ C, {f : _ A C | _ f}) p _).
  exists (hom_id A). exact _.
Defined.

Lemma pr1_isomorphism_path' {σ} {A B : Algebra σ} (p : A = B) :
  (isomorphism_path' A B p).1 = transport (λ C, Homomorphism A C) p (hom_id A).
Proof.
  by path_induction.
Defined.

Lemma path_transport_homomorphism {σ} {A B : Algebra σ}
  (p : A = B) (h : Homomorphism A A) s
  : transport (λ C, Homomorphism A C) p h s
    = transport (λ C, A s → C) (apD10 (ap carriers p) s) (h s).
Proof.
  by path_induction.
Defined.

Lemma path_ap_carriers_path_algebra `{Funext} {σ} {A B : Algebra σ}
  (p : carriers A = carriers B) T
  : ap carriers (path_algebra A B (p; T)) = p.
Proof.
  simpl in T.
  destruct A as [a α aH], B as [b β bH].
  simpl in *.
  destruct p, T.
  unfold path_algebra, path_sigma, path_sigma_hprop, istrunc_paths.
  simpl.
  by destruct trunc_equiv, center.
Qed.

Lemma path_path_sigalgebra `{Funext} {σ} (A B : SigAlgebra σ) (p q : A = B)
  (a : p..1 = q..1)
  : p = q.
Proof.
  unshelve eapply path_path_sigma; [exact a|].
  unshelve eapply path_path_sigma.
  apply @hprop_allpath.
  intros.
  apply @set_path2.
  apply @trunc_forall.
  exact _.
  intros.
  apply @trunc_operation.
  exact _.
  intros.
  apply B.2.2.
  apply @hprop_allpath.
  intros.
  apply @set_path2.
  exact _.
Qed.

Lemma path_path_algebra  `{Funext} {σ} (A B : Algebra σ) (p q : A = B)
  (a : ap carriers p = ap carriers q)
  : p = q.
Proof.
  set (e := Paths.equiv_ap (issig_algebra σ) A B).
  apply (ap e)^-1.
  apply path_path_sigalgebra.
  assert ((e.(equiv_fun) p) ..1 = ap carriers p) as P.
  induction p.
  reflexivity.
  assert (ap carriers q = (e.(equiv_fun) q) ..1) as Q.
  induction q.
  reflexivity.
  rewrite P.
  rewrite <- Q.
  exact a.
  (* exact (p @ a @ Q). *)
Qed.

Lemma path_ap_carriers_1 `{Univalence} {σ} (A : Algebra σ)
  : ap carriers (path_isomorphism (hom_id A)) = ap carriers 1.
Proof.
  rewrite path_ap_carriers_path_algebra.
  unfold path_equiv_family.
  unfold equiv_carriers_isomorphism.
  simpl.
  assert ((λ i : σ.(Sort),
@path_universe H (A.(carriers) i) (A.(carriers) i)
 (λ x : A.(carriers) i, x)
 (@isequiv_carriers_isomorphism σ A A (@hom_id σ A)
    (@is_isomorphism_id σ A) i)) =
    (λ i, 1%path)
  ).
  funext i.
  assert ((@isequiv_carriers_isomorphism σ A A (@hom_id σ A) 
 (@is_isomorphism_id σ A) i) = (isequiv_idmap _)).
 apply path_ishprop.
 rewrite X.
 apply path_universe_1.
 rewrite X.
 apply path_forall_1.
Defined.

Lemma path_path_isomorphism_id `{Univalence} {σ} (A : Algebra σ)
  : path_isomorphism (hom_id A) = 1%path.
Proof.
  unshelve eapply path_path_algebra.
  apply path_ap_carriers_1.
Defined.

Global Instance isequiv_isomorphism_path `{Univalence} {σ} (A B : Algebra σ)
  : IsEquiv (@isomorphism_path' σ A B).
Proof.
  refine (isequiv_adjointify (isomorphism_path' A B) (path_isomorphism' A B) _ _).
  - intros [f F].
    apply path_sigma_hprop.
    rewrite pr1_isomorphism_path'.
    simpl.
    apply path_homomorphism.
    intros s x.
    simpl.
    rewrite path_transport_homomorphism.
    simpl.
    rewrite transport_arrow_fromconst.
    unfold path_isomorphism'.
    rewrite path_ap_carriers_path_algebra.
    unfold path_equiv_family.
    simpl.
    rewrite apD10_path_forall.
    rewrite transport_path_universe.
    reflexivity.
  - intro p. induction p. simpl.
    apply path_path_isomorphism_id.
Qed.

Definition equiv_path_isomorphism `{Univalence} {σ} (A B : Algebra σ)
  : A = B <~> {f : Homomorphism A B | IsIsomorphism f}
  := BuildEquiv _ _ (isomorphism_path' A B) (isequiv_isomorphism_path A B).

Require Import HoTT.Categories.Category.Core.
Require Import HoTT.Categories.Category.Univalent.

Definition precategory_algebra `{Funext} (σ : Signature) : PreCategory.
Proof.
  apply (Build_PreCategory Homomorphism hom_id (@hom_compose σ)).
  - intros. apply path_homomorphism. intros s a. reflexivity.
  - intros. by apply path_homomorphism.
  - intros. by apply path_homomorphism.
  - intros A B. apply (trunc_equiv _ (issig_homomorphism A B)^-1).
Defined.

Lemma path_ap_homomorphism {σ} {A B : Algebra σ} {f g : Homomorphism A B}
  : f = g → ∀ s x, f s x = g s x.
Proof.
  intros p. by path_induction.
Defined.

Lemma equiv_isomorphic_isomorphic `{Funext} {σ} (A B : Algebra σ)
  : @Morphisms.Isomorphic (precategory_algebra σ) A B
    <~> {f : Homomorphism A B | IsIsomorphism f}.
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  - intros [f [a b c]].
    simpl in *.
    exists f.
    constructor.
    + intros s x y F.
      pose (path_ap_homomorphism b s).
      simpl in *.
      unfold Compose in p.
      pose (ap (a s) F) as q.
      rewrite (p x) in q.
      rewrite (p y) in q.
      exact q.
    + intros s.
      apply BuildIsSurjection. intros x.
      apply tr.
      exists (a s x).
      apply (path_ap_homomorphism c s x).
  - intros [f F].
    apply (@Morphisms.Build_Isomorphic (precategory_algebra σ) A B f).
    apply (@Morphisms.Build_IsIsomorphism (precategory_algebra σ) A B f (hom_inv f)).
    + apply path_homomorphism. intros s x. apply eissect.
    + apply path_homomorphism. intros s x. apply eisretr.
  - intros [f F]. apply path_sigma_hprop. reflexivity.
  - intros [f F]. apply Morphisms.path_isomorphic. reflexivity.
Defined.

Lemma equiv_idtoiso_idtoiso `{Funext} {σ} (A B : Algebra σ)
  : @Morphisms.idtoiso (precategory_algebra σ) A B = (equiv_isomorphic_isomorphic A B)^-1 ∘ isomorphism_path' A B.
Proof.
  funext p.
  induction p.
  apply Morphisms.path_isomorphic.
  reflexivity.
Defined.

Definition category_algebra `{Univalence} (σ : Signature) : Category.
Proof.
  apply (@Build_Category (precategory_algebra σ)).
  intros A B.
  rewrite equiv_idtoiso_idtoiso.
  apply isequiv_compose.
Defined.
