From stdpp Require Import prelude.
From AML Require Import Signature Expression.

Section sec_pattern.

Context
  [sign : signature]
  (Expression := @Expression sign)
  (expression_pattern := @expression_pattern sign).

Inductive Pattern : Type :=
| PEVar : EVar -> Pattern
| PSVar : SVar -> Pattern
| PBot : Pattern
| PImpl : Pattern -> Pattern -> Pattern
| PEx : EVar -> Pattern -> Pattern
| PMu : SVar -> Pattern -> Pattern
| PApp : Pattern -> Pattern -> Pattern
| POp : Sigma -> Pattern.

Definition pNeg (phi : Pattern) := PImpl phi PBot.
Definition pTop := pNeg PBot.
Definition pOr (phi psi : Pattern) := PImpl (pNeg phi) psi.
Definition pAnd (phi psi : Pattern) := pNeg (pOr (pNeg phi) (pNeg psi)).
Definition pIff (phi psi : Pattern) := pAnd (PImpl phi psi) (PImpl psi phi).
Definition pAll (x : EVar) (phi : Pattern) := pNeg (PEx x (pNeg phi)).

Definition finite_conjunction (phis : list Pattern) : Pattern :=
  foldr pAnd pTop phis.

Definition finite_disjunction (phis : list Pattern) : Pattern :=
  foldr pOr PBot phis.

#[export] Instance PatternDec : EqDecision Pattern.
Proof.
  intros x; induction x; intros []; try (by right; inversion 1).
  - destruct (decide (e = e0)); [by left; subst | by right; inversion 1].
  - destruct (decide (s = s0)); [by left; subst | by right; inversion 1].
  - by left.
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
| pa_bot : PatternAtomic PBot
| pa_op : forall o, PatternAtomic (POp o).

Fixpoint is_pattern_to_Pattern [e : Expression] (He : is_pattern e) : Pattern :=
  match He with
  | pattern_atomic a Ha =>
    match Ha with
    | atomic_evar x => PEVar x
    | atomic_svar X => PSVar X
    | atomic_cons c => POp c
    | atomic_bot => PBot
    end
  | pattern_app phi psi Hphi Hpsi => PApp (is_pattern_to_Pattern Hphi) (is_pattern_to_Pattern Hpsi)
  | pattern_impl phi psi Hphi Hpsi => PImpl (is_pattern_to_Pattern Hphi) (is_pattern_to_Pattern Hpsi)
  | pattern_ex x phi Hphi => PEx x (is_pattern_to_Pattern Hphi)
  | pattern_mu X phi Hphi => PMu X (is_pattern_to_Pattern Hphi)
  end.

Definition expression_pattern_to_Pattern (ep : expression_pattern) : Pattern :=
  is_pattern_to_Pattern (proj2_ep ep).

Fixpoint unparser (p : Pattern) : Expression :=
  match p with
  | PEVar x => [evar x]
  | PSVar X => [svar X]
  | PBot => [@bot sign]
  | PImpl p1 p2 => [@impl sign] ++ unparser p1 ++ unparser p2
  | PEx x p => [@ex sign; evar x] ++ unparser p
  | PMu X p => [@mu sign; svar X] ++ unparser p
  | PApp p1 p2 => [@app sign] ++ unparser p1 ++ unparser p2
  | POp c => [op c]
  end.

Lemma unparser_is_pattern (p : Pattern) : is_pattern (unparser p).
Proof.
  induction p; cbn.
  - by constructor 1; constructor.
  - by constructor 1; constructor.
  - by constructor 1; constructor.
  - by constructor 3.
  - by constructor 4.
  - by constructor 5.
  - by constructor 2.
  - by constructor 1; constructor.
Defined.

Lemma unparser_is_pattern_impl :
  forall phi psi,
    unparser_is_pattern (PImpl phi psi)
      =
    pattern_impl (unparser phi) (unparser psi) (unparser_is_pattern phi) (unparser_is_pattern psi).
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

Inductive SubPattern (chi : Pattern) : Pattern -> Prop :=
| sp_refl : SubPattern chi chi
| sp_app_left : forall phi psi, SubPattern chi phi -> SubPattern chi (PApp phi psi)
| sp_app_right : forall phi psi, SubPattern chi psi -> SubPattern chi (PApp phi psi)
| sp_impl_left : forall phi psi,  SubPattern chi phi -> SubPattern chi (PImpl phi psi)
| sp_impl_right : forall phi psi,  SubPattern chi psi -> SubPattern chi (PImpl phi psi)
| sp_ex : forall x phi, SubPattern chi phi -> SubPattern chi (PEx x phi)
| sp_mu : forall X phi, SubPattern chi phi -> SubPattern chi (PMu X phi)
.

Inductive AppContext : Type :=
| Hole
| LApp : AppContext -> Pattern -> AppContext
| RApp : Pattern -> AppContext -> AppContext.

Fixpoint csubst (c : AppContext) (phi :Pattern) : Pattern :=
  match c with
  | Hole => phi
  | LApp c psi => PApp (csubst c phi) psi
  | RApp psi c => PApp psi (csubst c phi)
  end.

End sec_pattern.
