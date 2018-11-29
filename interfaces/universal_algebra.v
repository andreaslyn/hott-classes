
(* XXX. This file has not been ported yet! *)

Require Import
  Coq.Unicode.Utf8
  HoTTClasses.implementations.list
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Basics.Equivalences.

Require Export HoTTClasses.interfaces.ua_basic.

Import ne_list.notations.
Import algebra_notations.

Section for_signature.
  Variable σ: Signature.

  Inductive Term (V : Type) : op_symbol_type σ → Type :=
    | Var: V → ∀ a, Term V (ne_list.one a)
    | App t y: Term V (ne_list.cons y t) → Term V (ne_list.one y) → Term V t
    | Op u: Term V (σ u).

  Arguments Var {V} _ _.

  Fixpoint map_var `(f: V → W) `(t: Term V u): Term W u :=
    match t in Term _ u return Term W u with
    | Var v s => Var (f v) s
    | App _ _ x y => App _ _ _ (map_var f x) (map_var f y)
    | Op s => Op _ s
    end.

  (* Term has OpType as an index, which means we can have terms with function
   types (no surprise there). However, often we want to prove properties that only speak
   of nullary terms: *)

  Definition Term0 v sort := Term v (ne_list.one sort).

  Section applications_ind.
    Context V (P: ∀ {a}, Term0 V a → Type).

    Arguments P {a} _.

    (* Proving such properties for nullary terms directly using Term's induction principle is
    problematic because it requires a property over terms of /any/ arity. Hence, we must first
     transform P into a statement about terms of all arities. Roughly speaking, we do this by
     saying [∀ x0...xN, P (App (... (App f x0) ...) xN)] for a term f of arity N. *)

    Fixpoint applications {ot}: Term V ot → Type :=
      match ot with
      | ne_list.one x => @P x
      | ne_list.cons x y => λ z, ∀ v, P v → applications (App V _ _ z v)
      end.

    (* To prove P/applications by induction, we can then use: *)

    Lemma applications_rect:
      (∀ v a, P (Var v a)) →
      (∀ u, applications (Op _ u)) →
      (∀ a (t: Term0 V a), P t).
    Proof.
     intros X0 X1 ??.
     cut (applications t).
      intros. assumption.
     induction t; simpl.
       apply X0.
      apply IHt1; exact IHt2.
     apply X1.
    Defined. (* todo: write as term *)

  End applications_ind.

  (* We parameterized Term over the index set for variables, because we will
   wants terms /with/ variables when speaking of identities in equational theories,
   but will want terms /without/ variables when constructing initial objects
   in variety categories generically in theory/ua_initial (which we get by taking
   False as the variable index set). *)

  Definition T := Term nat.
  Definition T0 := Term0 nat.

  Definition Identity t := prod (T t) (T t).
  Definition Identity0 sort := Identity (ne_list.one sort).
    (* While Identity0 is the one we usually have in mind, the generalized version for arbitrary op_types
     is required to make induction proofs work. *)

  Definition mkIdentity0 {sort}: T (ne_list.one sort) → T (ne_list.one sort) → Identity0 sort := pair.

  (* The laws in an equational theory will be entailments of identities for any of the sorts: *)

  Record Entailment (P: Type): Type := { entailment_premises: list P; entailment_conclusion: P }.

  Definition EqEntailment := Entailment (sigT Identity0).

  (* We also introduce a more general class of statements that we use to conveniently transfer
   statements between different models of a variety: *)

  Inductive Statement: Type :=
    | Eq t (i: Identity t)
    | Impl (a b: Statement)
    | Conj (a b: Statement)
    | Disj (a b: Statement)
    | Ext (P: Type).

  (* Statements are a strict generalization of EqEntailments. We cannot use the former for the laws,
   though, because they are too liberal (i.e. not equational) to support product varieties.
   We do have two injections: *)

  Definition identity_as_eq (s: sigT Identity0): Statement := Eq _ (projT2 s).
  Coercion identity_as_entailment sort (e: Identity0 sort): EqEntailment := Build_Entailment _ nil (existT _ _ e).

  Coercion entailment_as_statement (e: EqEntailment): Statement :=
     (fold_right Impl (identity_as_eq (entailment_conclusion _ e)) (map identity_as_eq (entailment_premises _ e))).

  Definition entailment_as_conjunctive_statement (e: EqEntailment): Statement :=
    Impl (fold_right Conj (Ext True) (map identity_as_eq (entailment_premises _ e)))
      (identity_as_eq (entailment_conclusion _ e)).

  (* The first one (the coercion) converts an entailment of the form (A, B, C |- D) into a statement of
   the form (A → B → C → D), while the second converts the same entailment into a statement of
   the form ((A ∧ B ∧ C) → D). Both have their uses in induction proofs. *)

  (* To be able to state that laws hold in a model of a variety, we must be able to evaluate terms
   using the model's implementation and using arbitrary variable assignments: *)

  Section Vars.
    Context (A : Carriers σ) (V : Type).

    Definition Vars := ∀ a, V → A a.
  End Vars.

  Definition no_vars x: Vars x False := λ _, False_rect _.

  (* Given an assignment mapping variables to closed terms, we can close open terms: *)

  Fixpoint close {V} {u} (v: Vars (λ x, Term False (ne_list.one x)) V) (t: Term V u): Term False u :=
    match t in Term _ u return Term False u with
    | Var x y => v y x
    | App x y z r => App _ x y (close v z) (close v r)
    | Op u => Op _ u
    end.

  Section eval.
    Context {A : Algebra σ}.

    Fixpoint eval {V} {n : op_symbol_type σ}
        (vars: Vars A V) (t: Term V n) {struct t}: op_type A n :=
      match t with
      | Var v a => vars a v
      | Op u => u^^A
      | App n a f p => eval vars f (eval vars p)
      end.

    Fixpoint app_tree {V} {u}: Term V u → op_type (Term0 V) u :=
      match u with
      | ne_list.one _ => id
      | ne_list.cons _ _ => λ x y, app_tree (App _ _ _ x y)
      end.

    Lemma eval_map_var `(f: V → W) v s (t: Term V s):
      eval v (map_var f t) = eval (λ s, v s ∘ f) t.
    Proof.
     induction t; simpl.
       reflexivity.
      rewrite <- IHt1, <- IHt2. reflexivity.
     reflexivity.
    Qed.

    Definition eval_stmt (vars: Vars A nat): Statement → Type :=
      fix F (s: Statement) :=
       match s with
       | Eq _ i => eval vars (fst i) = eval vars (snd i)
       | Impl a b => F a → F b
       | Ext P => P
       | Conj a b => F a ∧ F b
       | Disj a b => F a |_| F b
       end.

    Definition boring_eval_entailment (vars: Vars A nat) (ee: EqEntailment):
      eval_stmt vars ee ↔ eval_stmt vars (entailment_as_conjunctive_statement ee).
    Proof with auto.
      destruct ee. simpl.
      induction entailment_premises0; simpl; split; intros...
       destruct X0. apply IHentailment_premises0...
       apply IHentailment_premises0...
    Qed.

  End eval.
End for_signature.

(* And with that, we define equational theories and varieties: *)

Record EquationalTheory :=
  { et_sig:> Signature
  ; et_laws:> EqEntailment et_sig → Type }.

Class InVariety (et: EquationalTheory) : Type :=
  { variety_algebra :> Algebra et
  ; variety_laws : ∀ s, et_laws et s → ∀ vars, eval_stmt et vars s }.

Module notations.
  Global Infix "===" := (mkIdentity0 _) (at level 70, no associativity).
  Global Infix "-=>" := (Impl _) (at level 95, right associativity).
End notations.
