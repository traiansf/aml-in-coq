From stdpp Require Import prelude.
From AML Require Import Signature Expression.

Inductive Pattern `{signature} : Type :=
| PEVar : EVar -> Pattern
| PSVar : SVar -> Pattern
| PImpl : Pattern -> Pattern -> Pattern
| PEx : EVar -> Pattern -> Pattern
| μₚ : SVar -> Pattern -> Pattern
| PApp : Pattern -> Pattern -> Pattern
| POp : Sigma -> Pattern.

Section sec_pattern.

Context
  `{signature}.

Definition pBot := μₚ inhabitant (PSVar inhabitant).
Definition pNeg (ϕ : Pattern) := PImpl ϕ pBot.
Definition pTop := pNeg pBot.
Definition pOr (ϕ ψ : Pattern) := PImpl (pNeg ϕ) ψ.
Definition pAnd (ϕ ψ : Pattern) := pNeg (pOr (pNeg ϕ) (pNeg ψ)).
Definition pIff (ϕ ψ : Pattern) := pAnd (PImpl ϕ ψ) (PImpl ψ ϕ).
Definition pAll (x : EVar) (ϕ : Pattern) := pNeg (PEx x (pNeg ϕ)).

#[export] Instance Pattern_inhabited : Inhabited Pattern :=
  populate pBot.

Definition finite_conjunction (ϕs : list Pattern) : Pattern :=
  foldr pAnd pTop ϕs.

Definition finite_disjunction (ϕs : list Pattern) : Pattern :=
  foldr pOr pBot ϕs.

#[export] Instance PatternDec : EqDecision Pattern.
Proof.
  intros x; induction x; intros []; try (by right; inversion 1).
  - destruct (decide (e = e0)); [by left; subst | by right; inversion 1].
  - destruct (decide (s = s0)); [by left; subst | by right; inversion 1].
  - by destruct (IHx1 p); [destruct (IHx2 p0) |]; [left; subst | right; inversion 1..].
  - by destruct (decide (e = e0)); [destruct (IHx p) |];
      [left; subst | right; inversion 1..].
  - by destruct (decide (s = s0)); [destruct (IHx p) |];
      [left; subst | right; inversion 1..].
  - by destruct (IHx1 p); [destruct (IHx2 p0) |]; [left; subst | right; inversion 1..].
  - destruct (decide (s = s0)); [by left; subst | by right; inversion 1].
Qed.

Inductive PatternAtomic : Pattern -> Prop :=
| pa_evar : forall x, PatternAtomic (PEVar x)
| pa_svar : forall X, PatternAtomic (PSVar X)
| pa_op : forall o, PatternAtomic (POp o).

Fixpoint is_pattern_to_Pattern [e : Expression] (He : is_pattern e) : Pattern :=
  match He with
  | pattern_atomic a Ha =>
    match Ha with
    | atomic_evar x => PEVar x
    | atomic_svar X => PSVar X
    | atomic_cons c => POp c
    end
  | pattern_app ϕ ψ Hϕ Hψ => PApp (is_pattern_to_Pattern Hϕ) (is_pattern_to_Pattern Hψ)
  | pattern_impl ϕ ψ Hϕ Hψ => PImpl (is_pattern_to_Pattern Hϕ) (is_pattern_to_Pattern Hψ)
  | pattern_ex x ϕ Hϕ => PEx x (is_pattern_to_Pattern Hϕ)
  | pattern_mu X ϕ Hϕ => μₚ X (is_pattern_to_Pattern Hϕ)
  end.

Definition expression_pattern_to_Pattern (ep : expression_pattern) : Pattern :=
  is_pattern_to_Pattern (proj2_ep ep).

Fixpoint unparser (p : Pattern) : Expression :=
  match p with
  | PEVar x => [evar x]
  | PSVar X => [svar X]
  | PImpl p1 p2 => [impl] ++ unparser p1 ++ unparser p2
  | PEx x p => [ex; evar x] ++ unparser p
  | μₚ X p => [mu; svar X] ++ unparser p
  | PApp p1 p2 => [app] ++ unparser p1 ++ unparser p2
  | POp c => [op c]
  end.

Lemma unparser_is_pattern (p : Pattern) : is_pattern (unparser p).
Proof.
  induction p; cbn.
  - by constructor 1; constructor.
  - by constructor 1; constructor.
  - by constructor 3.
  - by constructor 4.
  - by constructor 5.
  - by constructor 2.
  - by constructor 1; constructor.
Defined.

Lemma unparser_is_pattern_impl :
  forall ϕ ψ,
    unparser_is_pattern (PImpl ϕ ψ)
      =
    pattern_impl (unparser ϕ) (unparser ψ) (unparser_is_pattern ϕ) (unparser_is_pattern ψ).
Proof. done. Qed.

Definition Pattern_to_expression_pattern (p : Pattern) : expression_pattern :=
  ep_intro (unparser p) (unparser_is_pattern p).

Lemma is_pattern_to_Pattern_unparser_eq :
  forall e (He : is_pattern e), unparser (is_pattern_to_Pattern He) = e.
Proof.
  intros e He; induction He; cbn.
  - by destruct a.
  - by rewrite IHHe1, IHHe2.
  - by rewrite IHHe1, IHHe2.
  - by rewrite IHHe.
  - by rewrite IHHe.
Qed.

Lemma expression_pattern_to_Pattern_to_expression_pattern :
  forall (ep : expression_pattern),
    Pattern_to_expression_pattern (expression_pattern_to_Pattern ep) = ep.
Proof. by intros [e He]; apply ep_eq_pi, is_pattern_to_Pattern_unparser_eq. Qed.

Lemma Pattern_to_expression_pattern_to_Pattern :
  forall (p : Pattern),
    expression_pattern_to_Pattern (Pattern_to_expression_pattern p) = p.
Proof.
  cbn. unfold unparser_is_pattern; induction p; cbn; try done.
  - by rewrite IHp1, IHp2.
  - by rewrite IHp.
  - by rewrite IHp.
  - by rewrite IHp1, IHp2.
Qed.

Inductive SubPattern (χ : Pattern) : Pattern -> Prop :=
| sp_refl : SubPattern χ χ
| sp_app_left : forall ϕ ψ, SubPattern χ ϕ -> SubPattern χ (PApp ϕ ψ)
| sp_app_right : forall ϕ ψ, SubPattern χ ψ -> SubPattern χ (PApp ϕ ψ)
| sp_impl_left : forall ϕ ψ,  SubPattern χ ϕ -> SubPattern χ (PImpl ϕ ψ)
| sp_impl_right : forall ϕ ψ,  SubPattern χ ψ -> SubPattern χ (PImpl ϕ ψ)
| sp_ex : forall x ϕ, SubPattern χ ϕ -> SubPattern χ (PEx x ϕ)
| sp_mu : forall X ϕ, SubPattern χ ϕ -> SubPattern χ (μₚ X ϕ)
.

Inductive AppContext : Type :=
| Hole
| LApp : AppContext -> Pattern -> AppContext
| RApp : Pattern -> AppContext -> AppContext.

Fixpoint csubst (c : AppContext) (ϕ :Pattern) : Pattern :=
  match c with
  | Hole => ϕ
  | LApp c ψ => PApp (csubst c ϕ) ψ
  | RApp ψ c => PApp ψ (csubst c ϕ)
  end.

End sec_pattern.

Declare Scope ml_scope.
Bind Scope ml_scope with signature.

Notation "x →ₚ y" := (PImpl x y) (at level 55, right associativity) : ml_scope.
Notation "¬ₚ x" := (pNeg x) (at level 40) : ml_scope.
Notation "x ∧ₚ y" := (pAnd x y) (at level 50, left associativity) : ml_scope.
Notation "x ∨ₚ y" := (pOr x y) (at level 53, left associativity) : ml_scope.
Notation "x ↔ₚ y" := (pIff x y) (at level 57, no associativity) : ml_scope.
Notation "⊥ₚ" := (pBot) (at level 37) : ml_scope.
Notation "⊤ₚ" := (pTop) (at level 37) : ml_scope.
Notation "∀ₚ x y" := (pAll x y) (at level 58, right associativity) : ml_scope.
Notation "∃ₚ x y" := (PEx x y) (at level 58, right associativity) : ml_scope.

Open Scope ml_scope.
