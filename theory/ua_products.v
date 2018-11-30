Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_basic
  HoTTClasses.theory.ua_homomorphisms
  HoTTClasses.implementations.ne_list
  HoTT.Types.Forall
  HoTT.Basics.Overture.

Import nel.notations algebra_notations.

Section prodalg.
  Context `{Funext} {σ : Signature} {I : Type} (A : I → Algebra σ).

  Definition carriers_prodalg : Carriers σ
    := λ (s : sigsort σ), ∀ (i : I), A i s.

  Fixpoint op_prodalg (w : opsym_type σ)
      : (∀ i, op_type (A i) w) → op_type carriers_prodalg w :=
    match w return (∀ i, op_type (A i) w) → op_type carriers_prodalg w with
    | [:_:] => idmap
    | _ ::: g => λ f p, op_prodalg g (λ i, f i (p i))
    end.

  Definition opfamily_prodalg (u : sigsym σ) : op_type carriers_prodalg (σ u)
    := op_prodalg (σ u) (λ i, u ^^ A i).

  Definition prodalg : Algebra σ
    := BuildAlgebra carriers_prodalg opfamily_prodalg.

  Definition fn_proj_prodalg (i:I) (s : sigsort σ) (x : prodalg s) : A i s
    := x i.

  Lemma oppreserving_proj_prodalg {w : opsym_type σ} (i : I)
    (sel : ∀ i : I, op_type (A i) w) (ao : op_type (A i) w) (P : sel i = ao)
    : OpPreserving (fn_proj_prodalg i) (op_prodalg w sel) ao.
  Proof.
    induction w.
    - exact P.
    - intro p.
      apply (IHw (λ i, sel i (p i)) (ao (p i))).
      exact (apD10 P (p i)).
  Qed.

  Global Instance ishomomorphism_proj_prodalg (i:I)
    : IsHomomorphism (fn_proj_prodalg i).
  Proof.
    intro u.
    by apply oppreserving_proj_prodalg.
  Qed.

  Definition hom_proj_prodalg (i : I) : Homomorphism prodalg (A i)
    := BuildHomomorphism (fn_proj_prodalg i).
End prodalg.

(* NOTE. Missing varieties section. *)
