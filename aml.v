From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude fin_sets.
From Coq Require Import Program.Equality FunctionalExtensionality RelationClasses.
From Coq Require Import Classical IndefiniteDescription.

Class signature : Type := {
  EVar : Type;
  EVar_infinite :> Infinite EVar;
  EVar_dec :> EqDecision EVar;
  SVar : Type;
  SVar_infinite :> Infinite SVar;
  SVar_dec :> EqDecision SVar;
  Sigma : Type;
  Sigma_dec :> EqDecision Sigma;
}.

Section fixed_signature.

Context `(signature).

Inductive Symbols : Type :=
| evar : EVar  -> Symbols
| svar : SVar -> Symbols
| bot : Symbols
| impl : Symbols
| ex : Symbols
| mu : Symbols
| app : Symbols
| op : Sigma -> Symbols.

Definition Expression : Type := list Symbols.

Inductive AtomicPattern : Expression -> Type :=
| atomic_evar : forall e : EVar, AtomicPattern [evar e]
| atomic_svar : forall e : SVar, AtomicPattern [svar e]
| atomic_cons : forall c : Sigma, AtomicPattern [op c]
| atomic_bot : AtomicPattern [bot].

Inductive is_pattern : Expression -> Type :=
| pattern_atomic : forall e, AtomicPattern e -> is_pattern e
| pattern_app : forall phi psi, is_pattern phi -> is_pattern psi ->
    is_pattern ([app] ++ phi ++ psi)
| pattern_impl : forall phi psi, is_pattern phi -> is_pattern psi ->
    is_pattern ([impl] ++ phi ++ psi)
| pattern_ex : forall (x : EVar) phi, is_pattern phi ->
    is_pattern ([ex] ++ [evar x] ++ phi)
| pattern_mu : forall (X : SVar) phi, is_pattern phi ->
    is_pattern ([mu] ++ [svar X] ++ phi).

Lemma empty_is_not_pattern : is_pattern [] -> False.
Proof. by inversion 1 as [a Ha | | | |]; inversion Ha. Qed.

Lemma singleton_is_pattern_atomic : forall a,
  is_pattern [a] -> AtomicPattern [a].
Proof.
  inversion 1 as
    [ p Hp | phi psi Hphi Hpsi | phi psi Hphi Hpsi
    | |
    ]; subst; [done |..];
    by apply app_nil in H1 as [-> ->];
       contradict Hphi; apply empty_is_not_pattern.
Qed.

Lemma singleton_is_pattern_atomic_rev : forall a,
  AtomicPattern [a] -> is_pattern [a].
Proof. by constructor 1. Qed.

Lemma unique_readibility_pos_length : forall p, is_pattern p -> length p > 0.
Proof. by inversion 1; [inversion X0 |..]; cbn; lia. Qed.

Lemma unique_readibility_initial_segment : forall e, is_pattern e ->
  forall p, strict prefix p e -> is_pattern p -> False.
Proof.
  intros e; remember (length e) as n; revert e Heqn.
  induction n using (well_founded_induction lt_wf); intros e Heqn He p Hpre Hp.
  destruct n; [by apply unique_readibility_pos_length in He; lia |].
  destruct e; [by inversion Heqn |].
  destruct Hpre as [[suf Hpre] Hproper].
  apply unique_readibility_pos_length in Hp as Hp_len.
  destruct p; [by cbn in Hp_len; lia | clear Hp_len].
  simplify_list_eq.
  destruct suf; [by contradict Hproper; simplify_list_eq | clear Hproper].
  inversion He; [by destruct p; inversion X|..]; subst; inversion Hp; subst.
  - by inversion X1.
  - simplify_list_eq.
    apply app_eq_app in H3 as [suf' Hpsi]; (destruct suf'; simplify_list_eq; cycle 1);
      [destruct Hpsi as [[-> Hpsi] | [-> Hpsi]] |].
    + contradict X1; eapply H0; cycle 2; [exact X | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite Hpsi, !app_length; cbn; rewrite app_length; cbn; lia.
    + contradict X; eapply H0; cycle 2; [exact X1 | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite !app_length; lia.
    + assert (phi = phi0 /\ psi = psi0 ++ s :: suf) as []
        by (destruct Hpsi; destruct_and!; done).
      clear Hpsi; subst.
      contradict X2; eapply H0; cycle 2; [exact X0 | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite !app_length; lia.
  - by inversion X1.
  - simplify_list_eq.
    apply app_eq_app in H3 as [suf' Hpsi]; (destruct suf'; simplify_list_eq; cycle 1);
      [destruct Hpsi as [[-> Hpsi] | [-> Hpsi]] |].
    + contradict X1; eapply H0; cycle 2; [exact X | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite Hpsi, !app_length; cbn; rewrite app_length; cbn; lia.
    + contradict X; eapply H0; cycle 2; [exact X1 | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite !app_length; lia.
    + assert (phi = phi0 /\ psi = psi0 ++ s :: suf) as []
        by (destruct Hpsi; destruct_and!; done).
      clear Hpsi; subst.
      contradict X2; eapply H0; cycle 2; [exact X0 | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite !app_length; lia.
  - by inversion X0.
  - simplify_list_eq.
    contradict X0; eapply H0; cycle 2; [exact X | split |  | done].
    + by eexists.
    + intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + by rewrite !app_length; lia.
  - by inversion X1.
  - simplify_list_eq.
    contradict X2; eapply H0; cycle 2; [exact X0 | split |  | done].
    + by eexists.
    + intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + by rewrite !app_length; lia.
Qed.

#[export] Instance AtomicPattern_proof_irrel :
  forall e, ProofIrrel (AtomicPattern e).
Proof. intros e [] He2; by dependent destruction He2. Qed.

#[export] Instance is_pattern_proof_irrel :
  forall e, ProofIrrel (is_pattern e).
Proof.
  intros e He1 .
  induction He1; intro He2; dependent destruction He2; try (by inversion a).
  - by rewrite (proof_irrel a a0).
  - apply app_eq_app in x0 as [suf' Hpsi]; (destruct suf'; simplify_list_eq; cycle 1);
      [destruct Hpsi as [[-> Hpsi] | [-> Hpsi]] |].
    + exfalso.
      eapply unique_readibility_initial_segment;
        [exact He2_1 | split; [by eexists |] | exact He1_1].
      intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + exfalso.
      eapply unique_readibility_initial_segment;
        [exact He1_1 | split; [by eexists |] | exact He2_1].
      intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + assert (phi0 = phi /\ psi0 = psi) as [-> ->]
        by (destruct Hpsi; destruct_and!; done).
      by rewrite (IHHe1_1 He2_1), (IHHe1_2 He2_2), x.
  - apply app_eq_app in x0 as [suf' Hpsi]; (destruct suf'; simplify_list_eq; cycle 1);
      [destruct Hpsi as [[-> Hpsi] | [-> Hpsi]] |].
    + exfalso.
      eapply unique_readibility_initial_segment;
        [exact He2_1 | split; [by eexists |] | exact He1_1].
      intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + exfalso.
      eapply unique_readibility_initial_segment;
        [exact He1_1 | split; [by eexists |] | exact He2_1].
      intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + assert (phi0 = phi /\ psi0 = psi) as [-> ->]
        by (destruct Hpsi; destruct_and!; done).
      by rewrite (IHHe1_1 He2_1), (IHHe1_2 He2_2), x.
  - by rewrite (IHHe1 He2).
  - by rewrite (IHHe1 He2).
Qed.

Inductive expression_pattern : Type :=
| ep_intro : forall e, is_pattern e -> expression_pattern.

Definition proj1_ep (ep : expression_pattern) : Expression :=
  match ep with
  | ep_intro e _ => e
  end.

Definition proj2_ep (ep : expression_pattern) : is_pattern (proj1_ep ep).
Proof. by destruct ep. Defined.

Lemma ep_eq_pi :
  forall (ep1 ep2 : expression_pattern), ep1 = ep2 <-> proj1_ep ep1 = proj1_ep ep2.
Proof.
  intros [] []; split; [by intros -> |].
  by cbn; intros ->; f_equal; apply proof_irrel.
Qed.

Inductive Pattern : Type :=
| PEVar : EVar -> Pattern
| PSVar : SVar -> Pattern
| PBot : Pattern
| PImpl : Pattern -> Pattern -> Pattern
| PEx : EVar -> Pattern -> Pattern
| PMu : SVar -> Pattern -> Pattern
| PApp : Pattern -> Pattern -> Pattern
| POp : Sigma -> Pattern.

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
  | PBot => [bot]
  | PImpl p1 p2 => [impl] ++ unparser p1 ++ unparser p2
  | PEx x p => [ex; evar x] ++ unparser p
  | PMu X p => [mu; svar X] ++ unparser p
  | PApp p1 p2 => [app] ++ unparser p1 ++ unparser p2
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

Context
  `{FinSet EVar EVarSet}
  `{FinSet SVar SVarSet}.

Inductive EVarFree (x : EVar) : Pattern -> Prop :=
| ef_evar : EVarFree x (PEVar x)
| ef_impl_left : forall phi psi, EVarFree x phi -> EVarFree x (PImpl phi psi)
| ef_impl_right : forall phi psi, EVarFree x psi -> EVarFree x (PImpl phi psi)
| ef_app_left : forall phi psi, EVarFree x phi -> EVarFree x (PApp phi psi)
| ef_app_right : forall phi psi, EVarFree x psi -> EVarFree x (PApp phi psi)
| ef_mu : forall X phi, EVarFree x phi -> EVarFree x (PMu X phi)
| ef_ex : forall y phi, EVarFree x phi -> y <> x -> EVarFree x (PEx y phi)
.

Inductive EVarBound (x : EVar) : Pattern -> Prop :=
| eb_impl_left : forall phi psi, EVarBound x phi -> EVarBound x (PImpl phi psi)
| eb_impl_right : forall phi psi, EVarBound x psi -> EVarBound x (PImpl phi psi)
| eb_app_left : forall phi psi, EVarBound x phi -> EVarBound x (PApp phi psi)
| eb_app_right : forall phi psi, EVarBound x psi -> EVarBound x (PApp phi psi)
| eb_mu : forall X phi, EVarBound x phi -> EVarBound x (PMu X phi)
| eb_ex_eq : forall phi, EVarBound x (PEx x phi)
| eb_ex_neq : forall y phi, EVarBound x phi -> EVarBound x (PEx y phi)
.

Inductive SVarFree (x : SVar) : Pattern -> Prop :=
| sf_svar : SVarFree x (PSVar x)
| sf_impl_left : forall phi psi, SVarFree x phi -> SVarFree x (PImpl phi psi)
| sf_impl_right : forall phi psi, SVarFree x psi -> SVarFree x (PImpl phi psi)
| sf_app_left : forall phi psi, SVarFree x phi -> SVarFree x (PApp phi psi)
| sf_app_right : forall phi psi, SVarFree x psi -> SVarFree x (PApp phi psi)
| sf_ex : forall X phi, SVarFree x phi -> SVarFree x (PEx X phi)
| sf_mu : forall y phi, SVarFree x phi -> y <> x -> SVarFree x (PMu y phi)
.

Inductive SVarBound (x : SVar) : Pattern -> Prop :=
| sb_impl_left : forall phi psi, SVarBound x phi -> SVarBound x (PImpl phi psi)
| sb_impl_right : forall phi psi, SVarBound x psi -> SVarBound x (PImpl phi psi)
| sb_app_left : forall phi psi, SVarBound x phi -> SVarBound x (PApp phi psi)
| sb_app_right : forall phi psi, SVarBound x psi -> SVarBound x (PApp phi psi)
| sb_ex : forall X phi, SVarBound x phi -> SVarBound x (PEx X phi)
| sb_mu_eq : forall phi, SVarBound x (PMu x phi)
| sb_mu_neq : forall y phi, SVarBound x phi -> SVarBound x (PMu y phi)
.

Fixpoint FEV (p : Pattern) : EVarSet :=
  match p with
  | PEVar x => {[x]}
  | PSVar X => ∅
  | PBot => ∅
  | POp _ => ∅
  | PImpl phi psi => FEV phi ∪ FEV psi
  | PApp phi psi => FEV phi ∪ FEV psi
  | PEx x phi => FEV phi ∖ {[x]}
  | PMu X phi => FEV phi
  end.

Lemma EVarFree_FEV : forall x p,
  EVarFree x p <-> x ∈ FEV p.
Proof.
  induction p; cbn.
  - by rewrite elem_of_singleton; split; inversion 1; constructor.
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - rewrite elem_of_union, <- IHp1, <- IHp2.
    by split; [inversion 1; [left | right] | intros []; [apply ef_impl_left | apply ef_impl_right]].
  - rewrite elem_of_difference, elem_of_singleton, <- IHp.
    by split; [inversion 1 | intros []; constructor].
  - rewrite <- IHp.
    by split; [inversion 1 | constructor].
  - rewrite elem_of_union, <- IHp1, <- IHp2.
    by split; [inversion 1; [left | right] | intros []; [apply ef_app_left | apply ef_app_right]].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
Qed.

#[export] Instance EVarFree_dec : RelDecision EVarFree.
Proof.
  by intros x p; destruct (elem_of_dec_slow x (FEV p)); [left | right];
    rewrite EVarFree_FEV.
Qed.

Fixpoint FSV (p : Pattern) : SVarSet :=
  match p with
  | PSVar x => {[x]}
  | PEVar X => ∅
  | PBot => ∅
  | POp _ => ∅
  | PImpl phi psi => FSV phi ∪ FSV psi
  | PApp phi psi => FSV phi ∪ FSV psi
  | PMu x phi => FSV phi ∖ {[x]}
  | PEx X phi => FSV phi
  end.

Lemma SVarFree_FSV : forall x p,
  SVarFree x p <-> x ∈ FSV p.
Proof.
  induction p; cbn.
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - by rewrite elem_of_singleton; split; inversion 1; constructor.
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - rewrite elem_of_union, <- IHp1, <- IHp2.
    by split; [inversion 1; [left | right] | intros []; [apply sf_impl_left | apply sf_impl_right]].
  - rewrite <- IHp.
    by split; [inversion 1 | constructor].
  - rewrite elem_of_difference, elem_of_singleton, <- IHp.
    by split; [inversion 1 | intros []; constructor].
  - rewrite elem_of_union, <- IHp1, <- IHp2.
    by split; [inversion 1; [left | right] | intros []; [apply sf_app_left | apply sf_app_right]].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
Qed.

#[export] Instance SVarFree_dec : RelDecision SVarFree.
Proof.
  by intros x p; destruct (elem_of_dec_slow x (FSV p)); [left | right];
    rewrite SVarFree_FSV.
Qed.

Fixpoint BEV (p : Pattern) : EVarSet :=
  match p with
  | PEVar _ => ∅
  | PSVar _ => ∅
  | PBot => ∅
  | POp _ => ∅
  | PImpl phi psi => BEV phi ∪ BEV psi
  | PApp phi psi => BEV phi ∪ BEV psi
  | PEx x phi => BEV phi ∪ {[x]}
  | PMu X phi => BEV phi
  end.

Lemma EVarBound_BEV : forall x p,
  EVarBound x p <-> x ∈ BEV p.
Proof.
  induction p; cbn.
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - rewrite elem_of_union, <- IHp1, <- IHp2.
    by split; [inversion 1; [left | right] | intros []; [apply eb_impl_left | apply eb_impl_right]].
  - rewrite elem_of_union, elem_of_singleton, <- IHp.
    split; [by inversion 1; [right | left] |].
    destruct (decide (x = e)) as [-> |]; [by intros; apply eb_ex_eq |].
    by intros []; [apply eb_ex_neq |].
  - rewrite <- IHp.
    by split; [inversion 1 | constructor].
  - rewrite elem_of_union, <- IHp1, <- IHp2.
    by split; [inversion 1; [left | right] | intros []; [apply eb_app_left | apply eb_app_right]].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
Qed.

#[export] Instance EVarBound_dec : RelDecision EVarBound.
Proof.
  by intros x p; destruct (elem_of_dec_slow x (BEV p)); [left | right];
    rewrite EVarBound_BEV.
Qed.

Definition EV (p : Pattern) : EVarSet := FEV p ∪ BEV p.
Definition EOccurs (x : EVar) (p : Pattern) : Prop := EVarFree x p \/ EVarBound x p.

Lemma EV_Eoccurs : forall x p, EOccurs x p <-> x ∈ EV p.
Proof.
  by intros; unfold EV; rewrite elem_of_union, <- EVarFree_FEV, <- EVarBound_BEV.
Qed.

Lemma EOccurs_impl x phi1 phi2 :
  EOccurs x (PImpl phi1 phi2) <-> EOccurs x phi1 \/ EOccurs x phi2.
Proof.
  rewrite EV_Eoccurs; unfold EV; cbn; rewrite! elem_of_union; unfold EOccurs.
  rewrite !EVarFree_FEV, !EVarBound_BEV.
  itauto.
Qed.

Lemma EOccurs_app x phi1 phi2 :
  EOccurs x (PApp phi1 phi2) <-> EOccurs x phi1 \/ EOccurs x phi2.
Proof.
  rewrite EV_Eoccurs; unfold EV; cbn; rewrite! elem_of_union.
  unfold EOccurs; rewrite !EVarFree_FEV, !EVarBound_BEV.
  itauto.
Qed.

Lemma EOccurs_ex x y phi :
  EOccurs x (PEx y phi) <-> x = y \/ EOccurs x phi.
Proof.
  rewrite EV_Eoccurs; unfold EV; cbn.
  rewrite! elem_of_union, elem_of_difference, elem_of_singleton.
  unfold EOccurs; rewrite !EVarFree_FEV, !EVarBound_BEV.
  destruct (decide (x = y)); itauto.
Qed.

Lemma EOccurs_mu x Y phi :
  EOccurs x (PMu Y phi) <-> EOccurs x phi.
Proof.
  rewrite EV_Eoccurs; unfold EV; cbn.
  rewrite! elem_of_union.
  unfold EOccurs; rewrite !EVarFree_FEV, !EVarBound_BEV.
  itauto.
Qed.

Inductive EOccursInd (x : EVar) : Pattern -> Prop :=
| eo_evar : EOccursInd x (PEVar x)
| eo_impl_left : forall phi1 phi2, EOccursInd x phi1 -> EOccursInd x (PImpl phi1 phi2)
| eo_impl_right : forall phi1 phi2, EOccursInd x phi2 -> EOccursInd x (PImpl phi1 phi2)
| eo_app_left : forall phi1 phi2, EOccursInd x phi1 -> EOccursInd x (PApp phi1 phi2)
| eo_app_right : forall phi1 phi2, EOccursInd x phi2 -> EOccursInd x (PApp phi1 phi2)
| eo_mu : forall Y phi, EOccursInd x phi -> EOccursInd x (PMu Y phi)
| eo_ex_eq : forall phi, EOccursInd x (PEx x phi)
| eo_ex_neq : forall y phi, EOccursInd x phi -> EOccursInd x (PEx y phi).

Lemma EOccursInd_iff x phi : EOccurs x phi <-> EOccursInd x phi.
Proof.
  induction phi.
  2,3,8: by split; [intros [Hx | Hx]; inversion Hx | inversion 1].
  - by split; [intros [Hx | Hx]; inversion Hx | inversion 1; left ]; constructor.
  - rewrite EOccurs_impl, IHphi1, IHphi2.
    by split; [intros []; constructor | inversion 1]; itauto.
  - rewrite EOccurs_ex, IHphi.
    split; [intros []; [subst; apply eo_ex_eq | apply eo_ex_neq] | inversion 1];
      itauto.
  - rewrite EOccurs_mu, IHphi.
    by split; [constructor | inversion 1].
  - rewrite EOccurs_app, IHphi1, IHphi2.
    by split; [intros []; constructor | inversion 1]; itauto.
Qed.

Fixpoint BSV (p : Pattern) : SVarSet :=
  match p with
  | PEVar _ => ∅
  | PSVar _ => ∅
  | PBot => ∅
  | POp _ => ∅
  | PImpl phi psi => BSV phi ∪ BSV psi
  | PApp phi psi => BSV phi ∪ BSV psi
  | PMu x phi => BSV phi ∪ {[x]}
  | PEx X phi => BSV phi
  end.

Lemma SVarBound_BSV : forall x p,
  SVarBound x p <-> x ∈ BSV p.
Proof.
  induction p; cbn.
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
  - rewrite elem_of_union, <- IHp1, <- IHp2.
    by split; [inversion 1; [left | right] | intros []; [apply sb_impl_left | apply sb_impl_right]].
  - rewrite <- IHp.
    by split; [inversion 1 | constructor].
  - rewrite elem_of_union, elem_of_singleton, <- IHp.
    split; [by inversion 1; [right | left] |].
    destruct (decide (x = s)) as [-> |]; [by intros; apply sb_mu_eq |].
    by intros []; [apply sb_mu_neq |].
  - rewrite elem_of_union, <- IHp1, <- IHp2.
    by split; [inversion 1; [left | right] | intros []; [apply sb_app_left | apply sb_app_right]].
  - by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
Qed.

#[export] Instance SVarBound_dec : RelDecision SVarBound.
Proof.
  by intros x p; destruct (elem_of_dec_slow x (BSV p)); [left | right];
    rewrite SVarBound_BSV.
Qed.

Definition SV (p : Pattern) : SVarSet := FSV p ∪ BSV p.
Definition SOccurs (x : SVar) (p : Pattern) : Prop := SVarFree x p \/ SVarBound x p.

Lemma SV_Soccurs : forall x p, SOccurs x p <-> x ∈ SV p.
Proof.
  by intros; unfold SV; rewrite elem_of_union, <- SVarFree_FSV, <- SVarBound_BSV.
Qed.

Lemma SOccurs_impl x phi1 phi2 :
  SOccurs x (PImpl phi1 phi2) <-> SOccurs x phi1 \/ SOccurs x phi2.
Proof.
  rewrite SV_Soccurs; unfold SV; cbn; rewrite! elem_of_union; unfold SOccurs.
  rewrite !SVarFree_FSV, !SVarBound_BSV.
  itauto.
Qed.

Lemma SOccurs_app x phi1 phi2 :
  SOccurs x (PApp phi1 phi2) <-> SOccurs x phi1 \/ SOccurs x phi2.
Proof.
  rewrite SV_Soccurs; unfold SV; cbn; rewrite! elem_of_union.
  unfold SOccurs; rewrite !SVarFree_FSV, !SVarBound_BSV.
  itauto.
Qed.

Lemma SOccurs_mu x y phi :
  SOccurs x (PMu y phi) <-> x = y \/ SOccurs x phi.
Proof.
  rewrite SV_Soccurs; unfold SV; cbn.
  rewrite! elem_of_union, elem_of_difference, elem_of_singleton.
  unfold SOccurs; rewrite !SVarFree_FSV, !SVarBound_BSV.
  destruct (decide (x = y)); itauto.
Qed.

Lemma SOccurs_ex x Y phi :
  SOccurs x (PEx Y phi) <-> SOccurs x phi.
Proof.
  rewrite SV_Soccurs; unfold SV; cbn.
  rewrite! elem_of_union.
  unfold SOccurs; rewrite !SVarFree_FSV, !SVarBound_BSV.
  itauto.
Qed.

Inductive SOccursInd (x : SVar) : Pattern -> Prop :=
| so_svar : SOccursInd x (PSVar x)
| so_impl_left : forall phi1 phi2, SOccursInd x phi1 -> SOccursInd x (PImpl phi1 phi2)
| so_impl_right : forall phi1 phi2, SOccursInd x phi2 -> SOccursInd x (PImpl phi1 phi2)
| so_app_left : forall phi1 phi2, SOccursInd x phi1 -> SOccursInd x (PApp phi1 phi2)
| so_app_right : forall phi1 phi2, SOccursInd x phi2 -> SOccursInd x (PApp phi1 phi2)
| so_ex : forall Y phi, SOccursInd x phi -> SOccursInd x (PEx Y phi)
| so_mu_eq : forall phi, SOccursInd x (PMu x phi)
| so_mu_neq : forall y phi, SOccursInd x phi -> SOccursInd x (PMu y phi).

Lemma SOccursInd_iff x phi : SOccurs x phi <-> SOccursInd x phi.
Proof.
  induction phi.
  1,3,8: by split; [intros [Hx | Hx]; inversion Hx | inversion 1].
  - by split; [intros [Hx | Hx]; inversion Hx | inversion 1; left ]; constructor.
  - rewrite SOccurs_impl, IHphi1, IHphi2.
    by split; [intros []; constructor | inversion 1]; itauto.
  - rewrite SOccurs_ex, IHphi.
    by split; [constructor | inversion 1].
  - rewrite SOccurs_mu, IHphi.
    split; [intros []; [subst; apply so_mu_eq | apply so_mu_neq] | inversion 1];
      itauto.
  - rewrite SOccurs_app, IHphi1, IHphi2.
    by split; [intros []; constructor | inversion 1]; itauto.
Qed.

Fixpoint evar_sub0 (x : EVar) (delta : Pattern) (p : Pattern) : Pattern :=
  match p with
  | PEVar y => if (decide (x = y)) then delta else p
  | PSVar _ => p
  | PBot => p
  | POp _ => p
  | PImpl phi psi => PImpl (evar_sub0 x delta phi) (evar_sub0 x delta psi)
  | PApp phi psi => PApp (evar_sub0 x delta phi) (evar_sub0 x delta psi)
  | PEx y phi =>  if (decide (x = y)) then p else PEx y (evar_sub0 x delta phi)
  | PMu X phi => PMu X (evar_sub0 x delta phi)
  end.

Lemma evar_sub0_id x phi : evar_sub0 x (PEVar x) phi = phi.
Proof.
  induction phi; cbn. 2,3,8: done.
  - by case_decide; subst.
  - by rewrite IHphi1, IHphi2.
  - by rewrite IHphi; case_decide.
  - by rewrite IHphi.
  - by rewrite IHphi1, IHphi2.
Qed.

Lemma SubPatternExBound z theta phi : SubPattern (PEx z theta) phi -> z ∈ BEV phi.
Proof.
  induction 1; cbn.
  - by cbn; rewrite elem_of_union, elem_of_singleton; right.
  - by apply elem_of_union; left.
  - by apply elem_of_union; right.
  - by apply elem_of_union; left.
  - by apply elem_of_union; right.
  - by apply elem_of_union; left.
  - done.
Qed.

Lemma SubPatternMuBound z theta phi : SubPattern (PMu z theta) phi -> z ∈ BSV phi.
Proof.
  induction 1; cbn.
  - by cbn; rewrite elem_of_union, elem_of_singleton; right.
  - by apply elem_of_union; left.
  - by apply elem_of_union; right.
  - by apply elem_of_union; left.
  - by apply elem_of_union; right.
  - done.
  - by apply elem_of_union; left.
Qed.

Record EFreeFor (x : EVar) (delta phi : Pattern) :=
{
  eff_evar : forall z, EVarFree z delta ->
    forall theta, SubPattern (PEx z theta) phi -> ~ EVarFree x theta;
  eff_svar : forall z, SVarFree z delta ->
    forall theta, SubPattern (PMu z theta) phi -> ~ EVarFree x theta
}.

Lemma EFreeForAtomic x delta a : PatternAtomic a -> EFreeFor x delta a.
Proof. by inversion 1; split; inversion 2. Qed.

Lemma EFreeForImpl x delta phi1 phi2 :
  EFreeFor x delta (PImpl phi1 phi2) <-> EFreeFor x delta phi1 /\ EFreeFor x delta phi2.
Proof.
  split; [intros [He Hs] | intros [[He1 Hs1] [He2 Hs2]]]; repeat split; intros z Hz theta Hsub.
  - by eapply He; [| apply sp_impl_left].
  - by eapply Hs; [| apply sp_impl_left].
  - by eapply He; [| apply sp_impl_right].
  - by eapply Hs; [| apply sp_impl_right].
  - by inversion_clear Hsub; [eapply He1 | eapply He2].
  - by inversion_clear Hsub; [eapply Hs1 | eapply Hs2].
Qed.

Lemma EFreeForApp x delta phi1 phi2 :
  EFreeFor x delta (PApp phi1 phi2) <-> EFreeFor x delta phi1 /\ EFreeFor x delta phi2.
Proof.
  split; [intros [He Hs] | intros [[He1 Hs1] [He2 Hs2]]]; repeat split; intros z Hz theta Hsub.
  - by eapply He; [| apply sp_app_left].
  - by eapply Hs; [| apply sp_app_left].
  - by eapply He; [| apply sp_app_right].
  - by eapply Hs; [| apply sp_app_right].
  - by inversion_clear Hsub; [eapply He1 | eapply He2].
  - by inversion_clear Hsub; [eapply Hs1 | eapply Hs2].
Qed.

Lemma EFreeForEx x delta y phi :
  EFreeFor x delta (PEx y phi) <-> EFreeFor x delta phi /\ (EVarFree y delta -> ~ EVarFree x phi).
Proof.
  split; [intros [He Hs] | intros [[He Hs] Hy]]; repeat split; intros.
  - by eapply He; [| apply sp_ex].
  - by eapply Hs; [| apply sp_ex].
  - by eapply He; [| apply sp_refl].
  - by inversion H17; subst; [apply Hy | eapply He].
  - by inversion H17; subst; eapply Hs.
Qed.

Lemma EFreeForMu x delta y phi :
  EFreeFor x delta (PMu y phi) <-> EFreeFor x delta phi /\ (SVarFree y delta -> ~ EVarFree x phi).
Proof.
  split; [intros [He Hs] | intros [[He Hs] Hy]]; repeat split; intros.
  - by eapply He; [| apply sp_mu].
  - by eapply Hs; [| apply sp_mu].
  - by eapply Hs; [| apply sp_refl].
  - by inversion H17; subst; eapply He.
  - by inversion H17; subst; [apply Hy | eapply Hs].
Qed.

Inductive EFreeForInd (x : EVar) (delta : Pattern) : Pattern -> Prop :=
| effi_evar : forall y, EFreeForInd x delta (PEVar y)
| effi_svar : forall Y, EFreeForInd x delta (PSVar Y)
| effi_bot : EFreeForInd x delta PBot
| effi_op : forall o, EFreeForInd x delta (POp o)
| effi_impl : forall phi1 phi2, EFreeForInd x delta phi1 -> EFreeForInd x delta phi2 ->
    EFreeForInd x delta (PImpl phi1 phi2)
| effi_app : forall phi1 phi2, EFreeForInd x delta phi1 -> EFreeForInd x delta phi2 ->
    EFreeForInd x delta (PApp phi1 phi2)
| effi_ex : forall y phi, EFreeForInd x delta phi -> (EVarFree y delta -> ~ EVarFree x phi) ->
    EFreeForInd x delta (PEx y phi)
| effi_mu : forall Y phi, EFreeForInd x delta phi -> (SVarFree Y delta -> ~ EVarFree x phi) ->
    EFreeForInd x delta (PMu Y phi).

Lemma EFreeForInd_iff x delta phi : EFreeFor x delta phi <-> EFreeForInd x delta phi.
Proof.
  induction phi.
  1-3,8: by split; [constructor | split; inversion 2].
  - rewrite EFreeForImpl, IHphi1, IHphi2.
    by split; [by intros []; constructor | inversion 1].
  - rewrite EFreeForEx, IHphi.
    by split; [by intros []; constructor | inversion 1].
  - rewrite EFreeForMu, IHphi.
    by split; [by intros []; constructor | inversion 1].
  - rewrite EFreeForApp, IHphi1, IHphi2.
    by split; [by intros []; constructor | inversion 1].
Qed.

Lemma EFreeForInd_x_not_occurs x delta phi (Hx : ~ EOccursInd x phi) : EFreeForInd x delta phi.
Proof.
  induction phi; cycle 5. 3-6 : by constructor.
  - constructor; [by apply IHphi; contradict Hx; constructor |].
    by intros _; contradict Hx; constructor; apply EOccursInd_iff; left.
  - by constructor; [apply IHphi1 | apply IHphi2]; contradict Hx;
      [apply eo_app_left | apply eo_app_right].
  - by constructor; [apply IHphi1 | apply IHphi2]; contradict Hx;
      [apply eo_impl_left | apply eo_impl_right].
  - constructor; [by apply IHphi; contradict Hx; constructor |].
    by intros _; contradict Hx; constructor; apply EOccursInd_iff; left.
Qed.

Lemma EFreeFor_x_y_if_not_bound x y phi (Hx : ~ EVarBound y phi) : EFreeFor x (PEVar y) phi.
Proof.
  split; [| by inversion 1].
  inversion 1; subst z; intros theta Hsub; contradict Hx.
  by eapply EVarBound_BEV, SubPatternExBound. 
Qed.
 

Fixpoint evar_rename (x y : EVar) (p : Pattern) : Pattern :=
  match p with
  | PEVar _ => p
  | PSVar _ => p
  | PBot => p
  | POp _ => p
  | PImpl phi psi => PImpl (evar_rename x y phi) (evar_rename x y psi)
  | PApp phi psi => PApp (evar_rename x y phi) (evar_rename x y psi)
  | PEx z phi =>
    if (decide (x = z))
      then (PEx y (evar_sub0 x (PEVar y) (evar_rename x y phi)))
      else PEx z (evar_rename x y phi)
  | PMu X phi => PMu X (evar_rename x y phi)
  end.

Lemma evar_rename_id x phi : evar_rename x x phi = phi.
Proof.
  induction phi; cbn. 1-3,8: done.
  - by rewrite IHphi1, IHphi2.
  - by rewrite IHphi, evar_sub0_id; case_decide; subst.
  - by rewrite IHphi.
  - by rewrite IHphi1, IHphi2.
Qed.

Definition evar_rename_iter (xs ys : list EVar) (p : Pattern) : Pattern :=
  foldr (fun (xy : EVar * EVar) (p : Pattern) => evar_rename xy.1 xy.2 p)
    p (zip xs ys).

Inductive OccursPositively (X : SVar) : Pattern -> Prop :=
| op_evar : forall x, OccursPositively X (PEVar x)
| op_svar : forall Y, OccursPositively X (PSVar Y)
| op_cons : forall c, OccursPositively X (POp c)
| op_bot : OccursPositively X PBot
| op_app : forall phi psi, OccursPositively X phi -> OccursPositively X psi ->
    OccursPositively X (PApp phi psi)
| op_ex : forall x phi, OccursPositively X phi -> OccursPositively X (PEx x phi)
| op_mu_eq : forall phi, OccursPositively X (PMu X phi)
| op_mu_neq : forall Y phi, Y <> X -> OccursPositively X phi ->
    OccursPositively X (PMu Y phi)
| op_impl : forall phi psi, OccursNegatively X phi -> OccursPositively X psi ->
    OccursPositively X (PImpl phi psi)
with OccursNegatively (X : SVar) : Pattern -> Prop :=
| on_evar : forall x, OccursNegatively X (PEVar x)
| on_svar : forall Y, Y <> X -> OccursNegatively X (PSVar Y)
| on_cons : forall c, OccursNegatively X (POp c)
| on_bot : OccursNegatively X PBot
| on_app : forall phi psi, OccursNegatively X phi -> OccursNegatively X psi ->
    OccursNegatively X (PApp phi psi)
| on_ex : forall x phi, OccursNegatively X phi -> OccursNegatively X (PEx x phi)
| on_mu_eq : forall phi, OccursNegatively X (PMu X phi)
| on_mu_neq : forall Y phi, Y <> X -> OccursNegatively X phi ->
    OccursNegatively X (PMu Y phi)
| on_impl : forall phi psi, OccursPositively X phi -> OccursNegatively X psi ->
    OccursNegatively X (PImpl phi psi)
.

Lemma evar_sub0_not_free x chi phi :
  ~ EVarFree x phi -> evar_sub0 x chi phi = phi.
Proof.
  induction phi; cbn; intro Hnfree; try done.
  - by case_decide; [subst; contradict Hnfree; constructor |].
  - rewrite IHphi1, IHphi2; [done |..];
      contradict Hnfree; apply EVarFree_FEV; cbn;
      rewrite elem_of_union, <- !EVarFree_FEV;
      [right | left].
  - by case_decide; [| rewrite IHphi; [| contradict Hnfree; constructor]].
  - by rewrite IHphi; [| contradict Hnfree; constructor].
  - by rewrite IHphi1, IHphi2; [done |..];
      contradict Hnfree; apply EVarFree_FEV; cbn;
      rewrite elem_of_union, <- !EVarFree_FEV;
      [right | left].
Qed.

Lemma evar_sub_rename_not_occurs x y phi :
  x <> y -> ¬ EOccursInd x (evar_sub0 x (PEVar y) (evar_rename x y phi)).
Proof.
  intros; induction phi; cbn. 2-4, 6-8: by inversion 1.
  - by case_decide; inversion 1.
  - case_decide; cbn; rewrite decide_False by done.
    + rewrite evar_sub0_not_free.
      * by contradict IHphi; inversion IHphi.
      * by contradict IHphi; apply EOccursInd_iff; left.
    + by contradict IHphi; inversion IHphi.
Qed.

Lemma evar_rename_FreeFor x y phi (Hxy : x <> y) (Hocc : ~ EOccursInd y phi) :
  EFreeForInd x (PEVar y) (evar_rename x y phi).
Proof.
  induction phi; cbn; intros; cycle 5. 3-6: by constructor.
  - feed specialize IHphi; [by contradict Hocc; apply eo_mu |].
    by constructor; [| inversion 1].
  - by constructor; [apply IHphi1 | apply IHphi2];
      contradict Hocc; [apply eo_app_left | apply eo_app_right].
  - by constructor; [apply IHphi1 | apply IHphi2];
      contradict Hocc; [apply eo_impl_left | apply eo_impl_right].
  - feed specialize IHphi; [by contradict Hocc; apply eo_ex_neq |].
    case_decide; [subst e |].
    + apply EFreeForInd_x_not_occurs.
      cut (~ EOccursInd x (evar_sub0 x (PEVar y) (evar_rename x y phi)));
        [rewrite <- !EOccursInd_iff, EOccurs_ex; itauto |].
      by apply evar_sub_rename_not_occurs.
    + constructor; [done |].
      by inversion 1; subst; contradict Hocc; constructor.
Qed.

Inductive SFreeForInd (x : SVar) (delta : Pattern) : Pattern -> Prop :=
| sffi_evar : forall y, SFreeForInd x delta (PEVar y)
| sffi_svar : forall Y, SFreeForInd x delta (PSVar Y)
| sffi_bot : SFreeForInd x delta PBot
| sffi_op : forall o, SFreeForInd x delta (POp o)
| sffi_impl : forall phi1 phi2, SFreeForInd x delta phi1 -> SFreeForInd x delta phi2 ->
    SFreeForInd x delta (PImpl phi1 phi2)
| sffi_app : forall phi1 phi2, SFreeForInd x delta phi1 -> SFreeForInd x delta phi2 ->
    SFreeForInd x delta (PApp phi1 phi2)
| sffi_ex : forall y phi, SFreeForInd x delta phi -> (EVarFree y delta -> ~ SVarFree x phi) ->
    SFreeForInd x delta (PEx y phi)
| sffi_mu : forall Y phi, SFreeForInd x delta phi -> (SVarFree Y delta -> ~ SVarFree x phi) ->
    SFreeForInd x delta (PMu Y phi).

Fixpoint svar_sub0 (x : SVar) (delta : Pattern) (p : Pattern) : Pattern :=
  match p with
  | PEVar _ => p
  | PSVar y => if (decide (x = y)) then delta else p
  | PBot => p
  | POp _ => p
  | PImpl phi psi => PImpl (svar_sub0 x delta phi) (svar_sub0 x delta psi)
  | PApp phi psi => PApp (svar_sub0 x delta phi) (svar_sub0 x delta psi)
  | PEx X phi => PEx X (svar_sub0 x delta phi)
  | PMu y phi =>  if (decide (x = y)) then p else PMu y (svar_sub0 x delta phi)
  end.

Lemma svar_sub0_not_free x chi phi :
  ~ SVarFree x phi -> svar_sub0 x chi phi = phi.
Proof.
  induction phi; cbn; intro Hnfree; try done.
  - by case_decide; [subst; contradict Hnfree; constructor |].
  - by rewrite IHphi1, IHphi2; [done |..];
      contradict Hnfree; apply SVarFree_FSV; cbn;
      rewrite elem_of_union, <- !SVarFree_FSV;
      [right | left].
  - by rewrite IHphi; [| contradict Hnfree; constructor].
  - by case_decide; [| rewrite IHphi; [| contradict Hnfree; constructor]].
  - by rewrite IHphi1, IHphi2; [done |..];
      contradict Hnfree; apply SVarFree_FSV; cbn;
      rewrite elem_of_union, <- !SVarFree_FSV;
      [right | left].
Qed.

Fixpoint svar_rename (x y : SVar) (p : Pattern) :=
  match p with
  | PEVar _ => p
  | PSVar _ => p
  | PBot => p
  | POp _ => p
  | PImpl phi psi => PImpl (svar_rename x y phi) (svar_rename x y psi)
  | PApp phi psi => PApp (svar_rename x y phi) (svar_rename x y psi)
  | PEx X phi => PEx X (svar_rename x y phi)
  | PMu z phi =>
    if (decide (x = z))
      then (PMu y (svar_sub0 x (PSVar y) (svar_rename x y phi)))
      else PMu z (svar_rename x y phi)
  end.

Definition svar_rename_iter (xs ys : list SVar) (p : Pattern) : Pattern :=
  foldr (fun (xy : SVar * SVar) (p : Pattern) => svar_rename xy.1 xy.2 p)
    p (zip xs ys).

Lemma SFreeForInd_x_not_occurs x delta phi (Hx : ~ SOccursInd x phi) : SFreeForInd x delta phi.
Proof.
  induction phi; cycle 6. 2-5 : by constructor.
  - by constructor; [apply IHphi1 | apply IHphi2]; contradict Hx;
      [apply so_app_left | apply so_app_right].
  - by constructor; [apply IHphi1 | apply IHphi2]; contradict Hx;
      [apply so_impl_left | apply so_impl_right].
  - constructor; [by apply IHphi; contradict Hx; constructor |].
    by intros _; contradict Hx; constructor; apply SOccursInd_iff; left.
  - constructor; [by apply IHphi; contradict Hx; constructor |].
    by intros _; contradict Hx; constructor; apply SOccursInd_iff; left.
Qed.

Lemma svar_sub_rename_not_occurs x y phi :
  x <> y -> ¬ SOccursInd x (svar_sub0 x (PSVar y) (svar_rename x y phi)).
Proof.
  intros; induction phi; cbn. 1,3-5, 7,8: by inversion 1.
  - by case_decide; inversion 1.
  - case_decide; cbn; rewrite decide_False by done.
    + rewrite svar_sub0_not_free.
      * by contradict IHphi; inversion IHphi.
      * by contradict IHphi; apply SOccursInd_iff; left.
    + by contradict IHphi; inversion IHphi.
Qed.

Lemma svar_rename_FreeFor x y phi (Hxy : x <> y) (Hocc : ~ SOccursInd y phi) :
  SFreeForInd x (PSVar y) (svar_rename x y phi).
Proof.
  induction phi; cbn; intros; cycle 6. 2-5: by constructor.
  - by constructor; [apply IHphi1 | apply IHphi2];
      contradict Hocc; [apply so_app_left | apply so_app_right].
  - by constructor; [apply IHphi1 | apply IHphi2];
      contradict Hocc; [apply so_impl_left | apply so_impl_right].
  - feed specialize IHphi; [by contradict Hocc; apply so_ex |].
    by constructor; [| inversion 1].
  - feed specialize IHphi; [by contradict Hocc; apply so_mu_neq |].
    case_decide; [subst s |].
    + apply SFreeForInd_x_not_occurs.
      cut (~ SOccursInd x (svar_sub0 x (PSVar y) (svar_rename x y phi)));
        [rewrite <- !SOccursInd_iff, SOccurs_mu; itauto |].
      by apply svar_sub_rename_not_occurs.
    + constructor; [done |].
      by inversion 1; subst; contradict Hocc; constructor.
Qed.

Section sec_fresh.

Context
  `{Infinite A}
  `{FinSet A SetA}.

Definition fresh_set (avoid : SetA) : A :=
  fresh (elements avoid).

Fixpoint fresh_set_iter (n : nat) (avoid : SetA) :=
  match n with
  | 0 => []
  | S n' =>
    let a' := fresh_set avoid in
      a' :: fresh_set_iter n' (avoid ∪ {[a']})
  end.

End sec_fresh.

Definition esubst (phi : Pattern) (x : EVar) (psi : Pattern) :=
  let phi_psi_evars := EV phi ∪ EV psi in
  let phi_psi_svars := SV phi ∪ SV psi in
  let bound_phi_psi_evars := elements (BEV phi ∩ EV psi) in
  let bound_phi_psi_svars := elements (BSV phi ∩ SV psi) in
  let fresh_evars := fresh_set_iter (length bound_phi_psi_evars) phi_psi_evars in
  let fresh_svars := fresh_set_iter (length bound_phi_psi_svars) phi_psi_svars in
  let etheta := evar_rename_iter bound_phi_psi_evars fresh_evars phi in
  let theta := svar_rename_iter bound_phi_psi_svars fresh_svars etheta in
  evar_sub0 x psi theta.

Definition ssubst (phi : Pattern) (x : SVar) (psi : Pattern) :=
  let phi_psi_evars := EV phi ∪ EV psi in
  let phi_psi_svars := SV phi ∪ SV psi in
  let bound_phi_psi_evars := elements (BEV phi ∩ EV psi) in
  let bound_phi_psi_svars := elements (BSV phi ∩ SV psi) in
  let fresh_evars := fresh_set_iter (length bound_phi_psi_evars) phi_psi_evars in
  let fresh_svars := fresh_set_iter (length bound_phi_psi_svars) phi_psi_svars in
  let etheta := evar_rename_iter bound_phi_psi_evars fresh_evars phi in
  let theta := svar_rename_iter bound_phi_psi_svars fresh_svars etheta in
  svar_sub0 x psi theta.

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

Definition pNeg (phi : Pattern) := PImpl phi PBot.
Definition pTop := pNeg PBot.
Definition pOr (phi psi : Pattern) := PImpl (pNeg phi) psi.
Definition pAnd (phi psi : Pattern) := pNeg (pOr (pNeg phi) (pNeg psi)).
Definition pIff (phi psi : Pattern) := pAnd (PImpl phi psi) (PImpl psi phi).
Definition pAll (x : EVar) (phi : Pattern) := pNeg (PEx x (pNeg phi)).
Definition pNu (X : SVar) (phi : Pattern) :=
  pNeg (PMu X (svar_sub0 X (pNeg (PSVar X)) phi)).

Definition finite_conjunction (phis : list Pattern) : Pattern :=
  foldr pAnd pTop phis.

Definition finite_disjunction (phis : list Pattern) : Pattern :=
  foldr pOr PBot phis.

Class Structure : Type :=
{
  idomain : Type;
  non_empty :> Inhabited idomain;
  Ensemble idomain : Type := idomain -> Prop;
  iapp : idomain -> idomain -> Ensemble idomain;
  isigma : Sigma -> Ensemble idomain
}.

Section fixed_structure.

Context `(Structure).

#[export] Instance pow_set_elem_of : ElemOf idomain Ensemble idomain := fun x A => A x.
#[export] Instance pow_set_empty : Empty Ensemble idomain := const False.
#[export] Instance pow_set_singleton : Singleton idomain Ensemble idomain :=
  fun x => fun y => y = x.
#[export] Instance pow_set_union : Union Ensemble idomain :=
  fun A B => fun x => x ∈ A \/ x ∈ B.
#[export] Instance pow_set_intersection : Intersection Ensemble idomain :=
  fun A B => fun x => x ∈ A /\ x ∈ B.
#[export] Instance pow_set_difference : Difference Ensemble idomain :=
  fun A B => fun x => x ∈ A /\ x ∉ B.
#[export] Instance pow_set_semiset : SemiSet idomain Ensemble idomain.
Proof. by split; [inversion 1 |..]. Qed.
#[export] Instance pow_set_set : Set_ idomain Ensemble idomain.
Proof. by split; [typeclasses eauto |..]. Qed.

Definition complement (A : Ensemble idomain) : Ensemble idomain := fun a => a ∉ A.
Definition top : Ensemble idomain := const true.

Lemma elem_of_equiv_top X : X ≡ top ↔ ∀ x, x ∈ X.
Proof. set_solver. Qed.

Lemma top_subseteq_equiv A : top ⊆ A <-> A ≡ top.
Proof. by split; intro Hsub; [split; [done |] | intro]; apply Hsub. Qed.

Definition filtered_union
    `(P : index -> Prop) (A : index -> Ensemble idomain) : Ensemble idomain :=
  fun a => exists i, P i /\ a ∈ A i.

Lemma elem_of_filtered_union
    a `(P : index -> Prop) (A : index -> Ensemble idomain) :
  a ∈ filtered_union P A <-> exists i, P i /\ a ∈ A i.
Proof. done. Qed.

Lemma member_of_filtered_union `(P : index -> Prop) (A : index -> Ensemble idomain) i :
  P i -> A i ⊆ filtered_union P A.
Proof. by intros Hi a HAi; apply elem_of_filtered_union; eexists. Qed.

Lemma empty_filtered_union `(P : index -> Prop) (A : index -> Ensemble idomain) :
  filtered_union P A ≡ ∅ <-> forall i, P i -> A i ≡ ∅.
Proof.
  split.
  - intros Hunion i; rewrite elem_of_equiv_empty; intros Hi a Ha.
    by apply (Hunion a), elem_of_filtered_union; eexists.
  - intro Hunion; rewrite elem_of_equiv_empty; intro a.
    rewrite elem_of_filtered_union; intros (? & ? & ?).
    by eapply Hunion.
Qed.

Definition indexed_union {index} : (index -> Ensemble idomain) -> Ensemble idomain :=
  filtered_union (const True).

Lemma elem_of_indexed_union a `(A : index -> Ensemble idomain) :
  a ∈ indexed_union A <-> exists i, a ∈ A i.
Proof.
  unfold indexed_union; rewrite elem_of_filtered_union.
  by split; intros [i Hi]; exists i; [apply Hi | split].
Qed.

Lemma member_of_indexed_union `(A : index -> Ensemble idomain) i :
  A i ⊆ indexed_union A.
Proof. by apply member_of_filtered_union. Qed.

Lemma empty_indexed_union `(A : index -> Ensemble idomain) :
  indexed_union A ≡ ∅ <-> forall i, A i ≡ ∅.
Proof.
  unfold indexed_union; rewrite empty_filtered_union.
  cbn; itauto.
Qed.

Definition filtered_intersection
    `(P : index -> Prop) (A : index -> Ensemble idomain) : Ensemble idomain :=
  fun a => forall i, P i -> a ∈ A i.

Lemma elem_of_filtered_intersection
    a `(P : index -> Prop) (A : index -> Ensemble idomain) :
  a ∈ filtered_intersection P A <-> forall i, P i -> a ∈ A i.
Proof. done. Qed.

Lemma member_of_filtered_intersection `(P : index -> Prop) (A : index -> Ensemble idomain) i :
  P i -> filtered_intersection P A ⊆ A i.
Proof. by intros Hi a; rewrite elem_of_filtered_intersection; intros HA; apply HA. Qed.

Lemma filtered_intersection_empty_top
    `(P : index -> Prop) (A : index -> Ensemble idomain) :
  (forall i, ~ P i) -> filtered_intersection P A ≡ top.
Proof.
  intros HnP; apply elem_of_equiv_top; intro a.
  apply elem_of_filtered_intersection; intros i HPi.
  by exfalso; eapply HnP.
Qed.

Definition indexed_intersection {index} : (index -> Ensemble idomain) -> Ensemble idomain :=
  filtered_intersection (const True).

Lemma elem_of_indexed_intersection a `(A : index -> Ensemble idomain) :
  a ∈ indexed_intersection A <-> forall i, a ∈ A i.
Proof.
  unfold indexed_intersection; rewrite elem_of_filtered_intersection.
  by split; intros Hall **; apply Hall.
Qed.

Lemma member_of_indexed_intersection `(A : index -> Ensemble idomain) i :
  indexed_intersection A ⊆ A i.
Proof. by apply member_of_filtered_intersection. Qed.

Definition intersection_list : list Ensemble idomain → Ensemble idomain := fold_right (∩) top.
Notation "⋂ l" := (intersection_list l) (at level 20, format "⋂ l") : stdpp_scope.

Lemma elem_of_intersection_list Xs x : x ∈ ⋂ Xs ↔ forall X, X ∈ Xs -> x ∈ X.
Proof.
  split.
  - induction Xs; simpl; intros HXs; [inversion 1|].
    setoid_rewrite elem_of_cons. rewrite elem_of_intersection in HXs. naive_solver.
  - induction Xs; intro HXs; [done |].
    simpl; apply elem_of_intersection; split; [apply HXs | apply IHXs]; [left |].
    by intros; apply HXs; right.
Qed.

Definition sym_diff (A B : Ensemble idomain) : Ensemble idomain := (A ∖ B) ∪ (B ∖ A).

#[export] Instance complement_subseteq_proper : Proper ((⊆) ==> flip (⊆)) complement.
Proof.
  intros B C Hbc a; unfold complement, elem_of, pow_set_elem_of.
  by intro Hb; contradict Hb; apply Hbc.
Qed.

#[export] Instance complement_equiv_proper : Proper ((≡) ==> (≡)) complement.
Proof.
  intros B C; rewrite !set_equiv_subseteq.
  intros [Hbc Hcb]; split.
  - by change (flip (⊆) (complement C) (complement B)); rewrite Hcb.
  - by change (flip (⊆) (complement B) (complement C)); rewrite Hbc.
Qed.

Lemma elem_of_complement a A : a ∈ complement A <-> a ∉ A.
Proof. done. Qed.

Lemma complement_top A : complement A ≡ top <-> A ≡ ∅.
Proof.
  split; [| intros ->].
  - intros Hcompl a; split; [| done]; intro Ha.
    destruct (Hcompl a) as [_ Hcompl'].
    by feed specialize Hcompl'.
  - by rewrite elem_of_equiv_top; intro; apply elem_of_complement, not_elem_of_empty.
Qed.

Lemma complement_twice_classic A : complement (complement A) ≡ A.
Proof.
  intro a; rewrite !elem_of_complement.
  split; [| by intros ? ?].
  by intro; apply NNPP.
Qed.

Lemma complement_empty_classic A : complement A ≡ ∅ <-> A ≡ top.
Proof.
  by rewrite <- complement_top, complement_twice_classic.
Qed.

Lemma complement_union_classic A B :
  complement (A ∪ B) ≡ complement A ∩ complement B.
Proof.
  intro a; rewrite elem_of_intersection, !elem_of_complement, elem_of_union.
  by split; [apply not_or_and | intros [] []].
Qed.

Lemma complement_intersection_classic A B :
  complement (A ∩ B) ≡ complement A ∪ complement B.
Proof.
  intro a; rewrite elem_of_union, !elem_of_complement, elem_of_intersection.
  by split; [apply not_and_or | intros [] []].
Qed.

Lemma complement_filtered_union `(P : index -> Prop) (A : index -> Ensemble idomain) :
  complement (filtered_union P A) ≡ filtered_intersection P (complement ∘ A).
Proof.
  intro x; rewrite elem_of_filtered_intersection; setoid_rewrite elem_of_complement;
    rewrite elem_of_filtered_union.
  split; [| by intros Hix (i & Hi & Hx); eapply Hix].
  by intros Hnix i Hi; contradict Hnix; eexists.
Qed.

Lemma complement_indexed_union `(f : index -> Ensemble idomain) :
  complement (indexed_union f) ≡ indexed_intersection (complement ∘ f).
Proof. by unfold indexed_union; rewrite complement_filtered_union. Qed.

Lemma complement_filtered_intersection_classic `(P : index -> Prop) `(A : index -> Ensemble idomain) :
  complement (filtered_intersection P A) ≡ filtered_union P (complement ∘ A).
Proof.
  intro x; rewrite elem_of_filtered_union; setoid_rewrite elem_of_complement;
    rewrite elem_of_filtered_intersection.
  split; [| by intros (i & Hi & Hx); contradict Hx; apply Hx].
  intros Hnot; apply not_all_ex_not in Hnot as [i Hnot].
  by eexists; apply imply_to_and in Hnot.
Qed.

Lemma complement_indexed_intersection_classic `(f : index -> Ensemble idomain) :
  complement (indexed_intersection f) ≡ indexed_union (complement ∘ f).
Proof.
  by unfold indexed_intersection; rewrite complement_filtered_intersection_classic.
Qed.

#[export]  Instance intersection_empty_l : LeftId (≡@{Ensemble idomain}) top (∩).
Proof. intros X. set_solver. Qed.
#[export] Instance intersection_empty_r : RightId (≡@{Ensemble idomain}) top (∩).
Proof. intros X. set_solver. Qed.

Lemma top_intersection A B : A ∩ B ≡ top <-> A ≡ top /\ B ≡ top.
Proof. set_solver. Qed.

Lemma top_filtered_intersection `(P : index -> Prop) (f : index -> Ensemble idomain) :
  filtered_intersection P f ≡ top
    <->
  forall B, P B -> f B ≡ top.
Proof.
  setoid_rewrite elem_of_equiv_top; setoid_rewrite elem_of_filtered_intersection.
  itauto.
Qed.

Lemma top_indexed_intersection (f : Ensemble idomain -> Ensemble idomain) :
  indexed_intersection f ≡ top
    <->
  forall B, f B ≡ top.
Proof.
  unfold indexed_intersection. rewrite top_filtered_intersection; cbn; itauto.
Qed.

Lemma intersection_list_cons X Xs : ⋂ (X :: Xs) = X ∩ ⋂ Xs.
Proof. done. Qed.

Lemma top_intersection_list Xs :
  ⋂ Xs ≡ top <-> Forall (fun X => X ≡ top) Xs.
Proof.
  induction Xs; [by cbn; split; [constructor |] |].
  by rewrite intersection_list_cons, top_intersection, Forall_cons, IHXs.
Qed.

Lemma difference_alt A B : A ∖ B ≡ A ∩ complement B.
Proof. set_solver. Qed.

Lemma subseteq_empty_difference_classic (X Y : Ensemble idomain) : X ⊆ Y <-> X ∖ Y ≡ ∅.
Proof.
  split; [apply subseteq_empty_difference |].
  intros Hxy a Ha; destruct (Hxy a) as [Hxy' _].
  rewrite elem_of_difference in Hxy'.
  destruct (classic (a ∈ Y)); [done | exfalso].
  by apply Hxy'.
Qed.

#[export] Instance sym_diff_proper : Proper ((≡) ==> (≡) ==> (≡)) sym_diff.
Proof. by intros A B Hab C D Hcd; unfold sym_diff; rewrite Hab, Hcd. Qed.

Lemma sym_diff_empty_classic A B : sym_diff A B ≡ ∅ <-> A ≡ B.
Proof.
  unfold sym_diff; split; [| intros ->].
  - intros Hab x; specialize (Hab x).
    rewrite elem_of_union, !elem_of_difference in Hab; split.
    + intros Ha.
      destruct (classic (x ∈ B)); [done |].
      by exfalso; apply Hab; left; split.
    + intros Hb.
      destruct (classic (x ∈ A)); [done |].
      by exfalso; apply Hab; right; split.
  - apply elem_of_equiv_empty; intro x.
    rewrite elem_of_union, !elem_of_difference.
    by intros [[] | []].
Qed.

Definition ext_iapp (B C : Ensemble idomain) : Ensemble idomain :=
  fun x => exists b, b ∈ B /\ exists c, c ∈ C /\ x ∈ iapp b c.

Lemma elem_of_ext_iapp a B C :
  a ∈ ext_iapp B C <-> exists b, b ∈ B /\ exists c, c ∈ C /\ a ∈ iapp b c.
Proof. done. Qed.

Lemma ext_iapp_empty_r : forall B, ext_iapp B ∅ ≡ ∅.
Proof.
  intros B; apply elem_of_equiv_empty.
  intros x (_ & _ & c & Hc & _); contradict Hc; eapply not_elem_of_empty.
Qed.

Lemma ext_iapp_empty_l : forall B, ext_iapp ∅ B ≡ ∅.
Proof.
  intros B; apply elem_of_equiv_empty.
  intros x (c & Hc & _); contradict Hc; eapply not_elem_of_empty.
Qed.

Lemma ext_iapp_union_l C D B :
  ext_iapp (C ∪ D) B ≡ ext_iapp C B ∪ ext_iapp D B.
Proof.
  intro a; rewrite elem_of_union; split.
  - intros (cd & Hcd & b & Hb & Ha); rewrite elem_of_union in Hcd.
    by destruct Hcd as [Hc | Hd]; [left | right]; repeat esplit.
  - intros [(c & Hc & b & Hb & Ha) | (d & Hd & b & Hb & Ha)];
      eexists; rewrite elem_of_union; split; [by left | | by right |];
      by repeat esplit.
Qed.

Lemma ext_iapp_union_r C D B :
  ext_iapp B (C ∪ D) ≡ ext_iapp B C ∪ ext_iapp B D.
Proof.
  intro a; rewrite elem_of_union; split.
  - intros (b & Hb & cd & Hcd & Ha); rewrite elem_of_union in Hcd.
    by destruct Hcd as [Hc | Hd]; [left | right]; repeat esplit.
  - intros [(b & Hb & c & Hc & Ha) | (b & Hb & d & Hd & Ha)];
      eexists; (split; [done |]); eexists; rewrite elem_of_union;
      split; [by left | | by right |];
      by repeat esplit.
Qed.

Lemma ext_iapp_intersection_l C D B :
  ext_iapp (C ∩ D) B ⊆ ext_iapp C B ∩ ext_iapp D B.
Proof.
  intro a; rewrite elem_of_intersection.
  intros (cd & Hcd & b & Hb & Ha); rewrite elem_of_intersection in Hcd.
  by destruct Hcd as [Hc Hd]; repeat esplit.
Qed.

Lemma ext_iapp_intersection_r C D B :
  ext_iapp B (C ∩ D) ⊆ ext_iapp B C ∩ ext_iapp B D.
Proof.
  intro a; rewrite elem_of_intersection.
  intros (b & Hb & cd & Hcd & Ha); rewrite elem_of_intersection in Hcd.
  by destruct Hcd as [Hc Hd]; repeat esplit.
Qed.

Lemma ext_iapp_filtered_union_l `(P : index -> Prop) (A : index -> Ensemble idomain) B :
  ext_iapp (filtered_union P A) B ≡ filtered_union P (fun i => ext_iapp (A i) B).
Proof.
  split.
  - by intros (a & (i & Hi & Ha) & b & Hb & Hx); repeat esplit.
  - by intros (i & Hi & ai & Hai & b & Hb & Hx); repeat esplit.
Qed.

Lemma ext_iapp_indexed_union_l `(A : index -> Ensemble idomain) B :
  ext_iapp (indexed_union A) B ≡ indexed_union (fun i => ext_iapp (A i) B).
Proof. by apply ext_iapp_filtered_union_l. Qed.

Lemma ext_iapp_filtered_union_r `(P : index -> Prop) (A : index -> Ensemble idomain) B :
  ext_iapp B (filtered_union P A) ≡ filtered_union P (fun i => ext_iapp B (A i)).
Proof.
  split.
  - by intros (b & Hb & a & (i & Hi & Ha) & Hx); repeat esplit.
  - by intros (i & b & Hb & Hi & ai & Hai & Hx); repeat esplit.
Qed.
Lemma ext_iapp_indexed_union_r `(A : index -> Ensemble idomain) B :
  ext_iapp B (indexed_union A) ≡ indexed_union (fun i => ext_iapp B (A i)).
Proof. by apply ext_iapp_filtered_union_r. Qed.

Lemma ext_iapp_filtered_intersection_l `(P : index -> Prop) (A : index -> Ensemble idomain) B :
  ext_iapp (filtered_intersection P A) B ⊆ filtered_intersection P (fun i => ext_iapp (A i) B).
Proof.
  intros x (a & Ha & b & Hb & Hx) i Hi.
  by exists a; split; [apply Ha | repeat esplit].
Qed.

Lemma ext_iapp_indexed_intersection_l `(A : index -> Ensemble idomain) B :
  ext_iapp (indexed_intersection A) B ⊆ indexed_intersection (fun i => ext_iapp (A i) B).
Proof. by apply ext_iapp_filtered_intersection_l. Qed.

Lemma ext_iapp_filtered_intersection_r `(P : index -> Prop) (A : index -> Ensemble idomain) B :
  ext_iapp B (filtered_intersection P A) ⊆ filtered_intersection P (fun i => ext_iapp B (A i)).
Proof.
  intros x (b & Hb & a & Ha & Hx) i Hi.
  exists b; split; [done |].
  by exists a; split; [apply Ha |].
Qed.

Lemma ext_iapp_indexed_intersection_r `(A : index -> Ensemble idomain) B :
  ext_iapp B (indexed_intersection A) ⊆ indexed_intersection (fun i => ext_iapp B (A i)).
Proof. by apply ext_iapp_filtered_intersection_r. Qed.

#[export] Instance ext_iapp_Proper_subseteq_l : Proper ((⊆) ==> (≡) ==> (⊆)) ext_iapp.
Proof.
  intros B C Hbc D E Hde.
  intros a (b & Hb & d & Hd & Ha).
  by exists b; split; [apply Hbc | exists d; split; [apply Hde |]].
Qed.

#[export] Instance ext_iapp_Proper_subseteq_r : Proper ((≡) ==> (⊆) ==> (⊆)) ext_iapp.
Proof.
  intros B C Hbc D E Hde.
  intros a (b & Hb & d & Hd & Ha).
  by exists b; split; [apply Hbc | exists d; split; [apply Hde |]].
Qed.

#[export] Instance ext_iapp_Proper_subseteq : Proper ((⊆) ==> (⊆) ==> (⊆)) ext_iapp.
Proof.
  intros B C Hbc D E Hde.
  by transitivity (ext_iapp B E); [rewrite Hde | rewrite Hbc].
Qed.

#[export] Instance ext_iapp_Proper : Proper ((≡) ==> (≡) ==> (≡)) ext_iapp.
Proof.
  intros B C Hbc D E Hde a; rewrite ! elem_of_ext_iapp.
  by setoid_rewrite Hbc; setoid_rewrite Hde.
Qed.

Lemma ext_iapp_complement_l B C D (Hbc : B ⊆ C) :
  ext_iapp (complement C) D ⊆ ext_iapp (complement B) D.
Proof.
  by eapply complement_subseteq_proper in Hbc; cbn in Hbc; rewrite Hbc.
Qed.

Lemma ext_iapp_complement_r B C D (Hbc : B ⊆ C) :
  ext_iapp D (complement C) ⊆ ext_iapp D (complement B).
Proof.
  by eapply complement_subseteq_proper in Hbc; cbn in Hbc; rewrite Hbc.
Qed.

Record Valuation : Type :=
{
  eval : EVar -> idomain;
  sval : SVar -> Ensemble idomain
}.

#[export] Instance ValudationInhabited : Inhabited Valuation :=
  populate {| eval := const inhabitant; sval := const ∅ |}.

Definition fn_update `{EqDecision A} `(f : A -> B) (a : A) (b : B) (x : A) : B :=
  if (decide (x = a)) then b else f x.

Lemma fn_update_id `{EqDecision A} `(f : A -> B) (a : A) :
  fn_update f a (f a) = f.
Proof. by extensionality x; unfold fn_update; case_decide; subst. Qed.

Lemma fn_update_eq `{EqDecision A} `(f : A -> B) a b :
  fn_update f a b a = b.
Proof. by unfold fn_update; rewrite decide_True by done. Qed.

Lemma fn_update_comm `{EqDecision A} `(f : A -> B) a1 b1 a2 b2 :
  a1 <> a2 ->
  fn_update (fn_update f a1 b1) a2 b2
    =
  fn_update (fn_update f a2 b2) a1 b1.
Proof.
  intro Ha; extensionality x; unfold fn_update.
  by do 2 case_decide; [congruence |..].
Qed.


Definition valuation_eupdate (e : Valuation) (x : EVar) (a : idomain) : Valuation :=
{|
  eval := fn_update (eval e) x a;
  sval := sval e
|}.

Lemma valuation_eupdate_id (e : Valuation) (x : EVar) :
  valuation_eupdate e x (eval e x) = e.
Proof.
  destruct e; unfold valuation_eupdate; cbn; f_equal; apply fn_update_id.
Qed.

Lemma valuation_eupdate_eq e x a : eval (valuation_eupdate e x a) x = a.
Proof. by destruct e; cbn; apply fn_update_eq. Qed.

Lemma valuation_eupdate_comm e x a y b :
  x <> y ->
  valuation_eupdate (valuation_eupdate e x a) y b
    =
  valuation_eupdate (valuation_eupdate e y b) x a.
Proof.
  intro Hxy; destruct e; unfold valuation_eupdate; cbn; f_equal.
  by apply fn_update_comm.
Qed.

Definition valuation_supdate (e : Valuation) (x : SVar) (a : Ensemble idomain) : Valuation :=
{|
  eval := eval e;
  sval := fn_update (sval e) x a
|}.

Lemma valuation_supdate_id (e : Valuation) (x : SVar) :
  valuation_supdate e x (sval e x) = e.
Proof.
  destruct e; unfold valuation_supdate; cbn; f_equal; apply fn_update_id.
Qed.

Lemma valuation_supdate_eq e x a : sval (valuation_supdate e x a) x = a.
Proof. by destruct e; cbn; apply fn_update_eq. Qed.

Lemma valuation_supdate_comm e x a y b :
  x <> y ->
  valuation_supdate (valuation_supdate e x a) y b
    =
  valuation_supdate (valuation_supdate e y b) x a.
Proof.
  intro Hxy; destruct e; unfold valuation_supdate; cbn; f_equal.
  by apply fn_update_comm.
Qed.

Lemma valuation_esupdate_comm e x a y b :
  valuation_supdate (valuation_eupdate e x a) y b
    =
  valuation_eupdate (valuation_supdate e y b) x a.
Proof. by destruct e. Qed.

Class PropositionalPatternValuation (F : Pattern -> Ensemble idomain) : Prop :=
{
  ppv_bot : F PBot ≡ ∅;
  ppv_impl : forall phi psi, F (PImpl phi psi) ≡ complement (F phi ∖ F psi);
}.

Section sec_propositional_pattern_valuation_props.
  Context
    (F : Pattern -> Ensemble idomain)
    `{PropositionalPatternValuation F}.

Lemma pattern_valuation_impl_alt_classic phi psi :
  F (PImpl phi psi) ≡ complement (F phi) ∪ F psi.
Proof.
  by rewrite ppv_impl, difference_alt,
    complement_intersection_classic, complement_twice_classic.
Qed.

Lemma pattern_valuation_neg_classic phi :
  F (pNeg phi) ≡ complement (F phi).
Proof.
  unfold pNeg.
  rewrite pattern_valuation_impl_alt_classic, ppv_bot.
  by apply union_empty_r.
Qed.

Lemma pattern_valuation_top : F pTop ≡ top.
Proof.
  unfold pTop; rewrite pattern_valuation_neg_classic, ppv_bot.
  by apply complement_top.
Qed.

Lemma pattern_valuation_or_classic phi psi :
  F (pOr phi psi) ≡ F phi ∪ F psi.
Proof.
  unfold pOr; rewrite pattern_valuation_impl_alt_classic, pattern_valuation_neg_classic.
  by rewrite complement_twice_classic.
Qed.

Lemma pattern_valuation_and_classic phi psi :
  F (pAnd phi psi) ≡ F phi ∩ F psi.
Proof.
  unfold pAnd.
  by rewrite pattern_valuation_neg_classic, pattern_valuation_or_classic,
    complement_union_classic, !pattern_valuation_neg_classic,
    !complement_twice_classic.
Qed.

Lemma pattern_valuation_iff_classic phi psi :
  F (pIff phi psi) ≡ complement (sym_diff (F phi) (F psi)).
Proof.
  unfold pIff.
  rewrite pattern_valuation_and_classic, !pattern_valuation_impl_alt_classic.
  by unfold sym_diff; rewrite complement_union_classic, !difference_alt,
    !complement_intersection_classic, !complement_twice_classic.
Qed.

Lemma pattern_valuation_iff_alt_classic phi psi :
  F (pIff phi psi) ≡ F (PImpl phi psi) ∩ F (PImpl psi phi).
Proof. by unfold pIff; rewrite pattern_valuation_and_classic. Qed.

Lemma pattern_valuation_finite_conjunction_classic (phis : list Pattern) :
  F (finite_conjunction phis) ≡ ⋂ (map F phis).
Proof.
  induction phis; unfold finite_conjunction.
  - by unfold foldr; rewrite pattern_valuation_top.
  - rewrite map_cons, intersection_list_cons, <- IHphis.
    by setoid_rewrite pattern_valuation_and_classic.
Qed.

Lemma pattern_valuation_finite_disjunction_classic (phis : list Pattern) :
  F (finite_disjunction phis) ≡ ⋃ (map F phis).
Proof.
  induction phis; unfold finite_disjunction; [by rewrite ppv_bot |].
  - rewrite map_cons, union_list_cons, <- IHphis.
    by setoid_rewrite pattern_valuation_or_classic.
Qed.

Lemma top_pattern_valuation_and_classic phi psi :
  F (pAnd phi psi) ≡ top <-> F phi ≡ top /\ F psi ≡ top.
Proof. by rewrite pattern_valuation_and_classic, top_intersection. Qed.

Lemma top_pattern_valuation_or_classic phi psi :
  F (pOr phi psi) ≡ top <-> F phi ∪ F psi ≡ top.
Proof. by rewrite pattern_valuation_or_classic. Qed.

Lemma top_pattern_valuation_impl_classic phi psi :
  F (PImpl phi psi) ≡ top <-> F phi ⊆ F psi.
Proof.
  rewrite ppv_impl, complement_top.
  by symmetry; apply subseteq_empty_difference_classic.
Qed.

Lemma top_pattern_valuation_neg_classic phi :
  F (pNeg phi) ≡ top <-> F phi ≡ ∅.
Proof.
  unfold pNeg; rewrite top_pattern_valuation_impl_classic, ppv_bot.
  rewrite set_equiv_subseteq; split; intro Hsub; [| by apply Hsub].
  by split; [| apply empty_subseteq].
Qed.

Lemma top_pattern_valuation_iff_classic phi psi :
  F (pIff phi psi) ≡ top <-> F phi ≡ F psi.
Proof.
  by unfold pIff; rewrite top_pattern_valuation_and_classic,
    !top_pattern_valuation_impl_classic, set_equiv_subseteq.
Qed.

Lemma top_pattern_valuation_finite_conjunction_classic (phis : list Pattern) :
  F (finite_conjunction phis) ≡ top <-> Forall (fun phi => F phi ≡ top) phis.
Proof.
  by rewrite pattern_valuation_finite_conjunction_classic, top_intersection_list, Forall_map.
Qed.

End sec_propositional_pattern_valuation_props.

Fixpoint pattern_valuation (e : Valuation) (p : Pattern) : Ensemble idomain :=
  match p with
  | PEVar x => {[eval e x]}
  | PSVar X => sval e X
  | POp o => isigma o
  | PBot => ∅
  | PApp phi psi => ext_iapp (pattern_valuation e phi) (pattern_valuation e psi)
  | PImpl phi psi => complement (pattern_valuation e phi ∖ pattern_valuation e psi)
  | PEx x phi => indexed_union (fun a => pattern_valuation (valuation_eupdate e x a) phi)
  | PMu X phi => filtered_intersection (fun B => pattern_valuation (valuation_supdate e X B) phi ⊆ B) id
  end.

#[export] Instance propositional_pattern_valuation e :
  PropositionalPatternValuation (pattern_valuation e).
Proof. by constructor. Qed.

Lemma pattern_valuation_forall_classic e x phi :
  pattern_valuation e (pAll x phi)
    ≡
  indexed_intersection (fun a => pattern_valuation (valuation_eupdate e x a) phi).
Proof.
  unfold pAll; rewrite pattern_valuation_neg_classic by done; cbn.
  rewrite complement_indexed_union.
  intro a; rewrite !elem_of_indexed_intersection; cbn.
  apply forall_proper; intro a_x; rewrite complement_twice_classic, elem_of_difference.
  by split; [intros [] | intro; split; [| apply not_elem_of_empty]].
Qed.

Record FV_equal (e1 e2 : Valuation) (phi : Pattern) : Prop :=
{
  fve_evar : forall x, EVarFree x phi -> eval e1 x = eval e2 x;
  fve_svar : forall X, SVarFree X phi -> sval e1 X = sval e2 X;
}.

Lemma pattern_valuation_fv phi :
  forall e1 e2, FV_equal e1 e2 phi ->
    pattern_valuation e1 phi ≡ pattern_valuation e2 phi.
Proof.
  induction phi; cbn; intros e1 e2 [].
  - by rewrite fve_evar0; [| constructor].
  - by rewrite fve_svar0; [| constructor].
  - done.
  - rewrite IHphi1, IHphi2; [done |..]; split; intros.
    + by apply fve_evar0, ef_impl_right.
    + by apply fve_svar0, sf_impl_right.
    + by apply fve_evar0, ef_impl_left.
    + by apply fve_svar0, sf_impl_left.
  - intro b; rewrite !elem_of_indexed_union.
    cut (forall i : idomain, pattern_valuation (valuation_eupdate e1 e i) phi
      ≡ pattern_valuation (valuation_eupdate e2 e i) phi);
      [by intro Hrew; setoid_rewrite Hrew |].
    intro a; rewrite IHphi; [done |].
    split; intros x Hx.
    + cbn; unfold fn_update; case_decide; [done |].
      by apply fve_evar0; constructor.
    + by apply fve_svar0; constructor.
  - intro a; rewrite !elem_of_filtered_intersection.
    apply forall_proper; intro A.
    rewrite IHphi; [done |].
    split; intros x Hx.
    + by apply fve_evar0; constructor.
    + cbn; unfold fn_update; case_decide; [done |].
      by apply fve_svar0; constructor.
  - intro a; rewrite !elem_of_ext_iapp.
    setoid_rewrite (IHphi1 e1 e2); [setoid_rewrite (IHphi2 e1 e2) |]; [done |..];
      split; intros.
    + by apply fve_evar0, ef_app_right.
    + by apply fve_svar0, sf_app_right.
    + by apply fve_evar0, ef_app_left.
    + by apply fve_svar0, sf_app_left.
  - done.
Qed.

Definition esatisfies e phi := pattern_valuation e phi ≡ top.

Lemma esatisfies_evar e x : esatisfies e (PEVar x) <-> exists a, top ≡ {[a]}.
Proof.
  unfold esatisfies; cbn; split; [by eexists |].
  intros [a Ha] _a; split; [done |].
  assert (He : eval e x ∈ top) by done.
  rewrite Ha, !elem_of_singleton in *; congruence.
Qed.

Lemma esatisfies_svar e X : esatisfies e (PSVar X) <-> sval e X ≡ top.
Proof. done. Qed.

Lemma esatisfies_cons e op : esatisfies e (POp op) <-> isigma op ≡ top.
Proof. done. Qed.

Lemma esatisfies_bot e : ~ esatisfies e PBot.
Proof.
  intros contra. destruct (contra inhabitant) as [_ contra'].
  by apply contra'.
Qed.

Lemma esatisfies_top e : esatisfies e pTop.
Proof. by apply pattern_valuation_top. Qed.

Lemma esatisfies_neg_classic e phi : esatisfies e (pNeg phi) <-> pattern_valuation e phi ≡ ∅.
Proof. by apply top_pattern_valuation_neg_classic. Qed.

Lemma esatisfies_app e phi psi :
  esatisfies e (PApp phi psi)
    <->
  ext_iapp (pattern_valuation e phi) (pattern_valuation e psi) ≡ top.
Proof. done. Qed.

Lemma esatisfies_and_classic e phi psi :
  esatisfies e (pAnd phi psi) <-> esatisfies e phi /\ esatisfies e psi.
Proof. by apply top_pattern_valuation_and_classic. Qed.

Lemma esatisfies_or_classic e phi psi :
  esatisfies e (pOr phi psi)
    <->
  pattern_valuation e phi ∪ pattern_valuation e psi ≡ top.
Proof. by apply top_pattern_valuation_or_classic. Qed.

Lemma esatisfies_impl_classic e phi psi :
  esatisfies e (PImpl phi psi)
    <->
  pattern_valuation e phi ⊆ pattern_valuation e psi.
Proof. by apply top_pattern_valuation_impl_classic. Qed.

Lemma esatisfies_iff_classic e phi psi :
  esatisfies e (pIff phi psi)
    <->
  pattern_valuation e phi ≡ pattern_valuation e psi.
Proof. by apply top_pattern_valuation_iff_classic. Qed.

Lemma esatisfies_iff_alt_classic e phi psi :
  esatisfies e (pIff phi psi)
    <->
  esatisfies e (PImpl phi psi) /\ esatisfies e (PImpl psi phi).
Proof. by apply esatisfies_and_classic. Qed.

Lemma esatisfies_ex e x phi :
  esatisfies e (PEx x phi)
    <->
  indexed_union (fun a => pattern_valuation (valuation_eupdate e x a) phi) ≡ top.
Proof. done. Qed.

Lemma esatisfies_ex_elim e x phi :
  (exists a, esatisfies (valuation_eupdate e x a) phi) -> esatisfies e (PEx x phi).
Proof.
  rewrite esatisfies_ex.
  intros [a Ha]; rewrite elem_of_equiv_top; intro b.
  rewrite elem_of_indexed_union.
  by exists a; apply Ha.
Qed.

Lemma esatisfies_all_classic e x phi :
  esatisfies e (pAll x phi)
    <->
  forall a, esatisfies (valuation_eupdate e x a) phi.
Proof.
  unfold pAll; rewrite esatisfies_neg_classic; cbn.
  rewrite empty_indexed_union.
  apply forall_proper; intro a.
  by rewrite complement_empty_classic, difference_empty .
Qed.

Lemma esatisfies_mu_elim e X phi :
  (forall B, esatisfies (valuation_supdate e X B) phi) -> esatisfies e (PMu X phi).
Proof.
  unfold esatisfies; cbn; setoid_rewrite elem_of_equiv_top.
  intros Hall a; apply elem_of_filtered_intersection; intros B HB.
  by apply HB, Hall.
Qed.

Lemma esatisfies_finite_conjunction_classic e phis :
  esatisfies e (finite_conjunction phis) <-> Forall (esatisfies e) phis.
Proof. by apply top_pattern_valuation_finite_conjunction_classic. Qed.

Lemma esatisfies_finite_disjunction_classic e phis :
  esatisfies e (finite_disjunction phis)
    <->
  ⋃ (map (pattern_valuation e) phis) ≡ top.
Proof.
  by unfold esatisfies; rewrite pattern_valuation_finite_disjunction_classic.
Qed.

Definition satisfies (phi : Pattern) : Prop := forall e, esatisfies e phi.

Lemma satisfies_evar x : satisfies (PEVar x) <-> exists a, top ≡ {[a]}.
Proof.
  split; intros He.
  - by eapply esatisfies_evar with (e := inhabitant), He.
  - by intro e; apply esatisfies_evar.
Qed.

Lemma satisfies_cons op : satisfies (POp op) <-> isigma op ≡ top.
Proof.
  split; intros He.
  - by apply He with (e := inhabitant).
  - by intro e; apply esatisfies_cons.
Qed.

Lemma satisfies_bot : ~ satisfies PBot.
Proof.
  by intros He; apply esatisfies_bot with inhabitant, He.
Qed.

Lemma satisfies_top : satisfies pTop.
Proof.
  by intro; apply esatisfies_top.
Qed.

Lemma satisfies_and_classic phi psi :
  satisfies (pAnd phi psi) <-> satisfies phi /\ satisfies psi.
Proof.
  by unfold satisfies; setoid_rewrite esatisfies_and_classic; firstorder.
Qed.

Lemma satisfies_mp_classic phi psi :
  satisfies (PImpl phi psi) -> satisfies phi -> satisfies psi.
Proof.
  unfold satisfies; setoid_rewrite esatisfies_impl_classic.
  unfold esatisfies; setoid_rewrite elem_of_equiv_top.
  by intros Hsub Hphi e a; apply Hsub, Hphi.
Qed.

Lemma satisfies_iff_alt_classic phi psi :
  satisfies (pIff phi psi)
    <->
  satisfies (PImpl phi psi) /\ satisfies (PImpl psi phi).
Proof.
  unfold satisfies; setoid_rewrite esatisfies_iff_alt_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma satisfies_all_classic x phi :
  satisfies (pAll x phi) <-> satisfies phi.
Proof.
  split; intros Hsat e; cycle 1.
  - by apply esatisfies_all_classic; intro; apply Hsat.
  - specialize (Hsat e); rewrite esatisfies_all_classic in Hsat.
    specialize (Hsat (eval e x)).
    by rewrite valuation_eupdate_id in Hsat.
Qed.

Lemma satisfies_finite_conjunction_classic phis :
  satisfies (finite_conjunction phis) <-> Forall satisfies phis.
Proof.
  unfold satisfies; setoid_rewrite esatisfies_finite_conjunction_classic.
  setoid_rewrite Forall_forall.
  itauto.
Qed.

End fixed_structure.

Definition valid (phi : Pattern) : Prop :=
  forall (s : Structure), satisfies s phi.

Lemma valid_top : valid pTop.
Proof. by intro; apply satisfies_top. Qed.

Lemma valid_and_classic (phi psi : Pattern) :
  valid (pAnd phi psi) <-> valid phi /\ valid psi.
Proof.
  unfold valid; setoid_rewrite satisfies_and_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma valid_iff_alt_classic (phi psi : Pattern) :
  valid (pIff phi psi) <-> valid (PImpl phi psi) /\ valid (PImpl psi phi).
Proof.
  unfold valid; setoid_rewrite satisfies_iff_alt_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma valid_mp_classic (phi psi : Pattern) :
  valid (PImpl phi psi) -> valid phi -> valid psi.
Proof.
  intros Himpl Hphi s.
  eapply satisfies_mp_classic; [apply Himpl | apply Hphi].
Qed.

Lemma valid_iff_classic (phi psi : Pattern) :
  valid (pIff phi psi) -> (valid phi <-> valid psi).
Proof.
  rewrite valid_iff_alt_classic; intros [Himpl Himpl'].
  by split; apply valid_mp_classic.
Qed.

Lemma valid_finite_conjunction_classic phis :
  valid (finite_conjunction phis) <-> Forall valid phis.
Proof.
  unfold valid; setoid_rewrite satisfies_finite_conjunction_classic.
  setoid_rewrite Forall_forall.
  itauto.
Qed.

Definition global_semantic_consequence (phi psi : Pattern) : Prop :=
  forall (s : Structure), satisfies s phi -> satisfies s psi.

Definition globally_logically_equivalent (phi psi : Pattern) : Prop :=
  forall (s : Structure), satisfies s phi <-> satisfies s psi.

Lemma globally_logically_equivalent_iff phi psi :
  globally_logically_equivalent phi psi
    <->
  global_semantic_consequence phi psi /\ global_semantic_consequence psi phi.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intro; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

#[export] Instance global_semantic_consequence_satisfies s :
  Proper (global_semantic_consequence ==> Basics.impl) (satisfies s).
Proof. by intros phi psi Hcns Hphi; apply Hcns, Hphi. Qed.

#[export] Instance global_semantic_consequence_valid :
  Proper (global_semantic_consequence ==> Basics.impl) valid.
Proof. intros phi psi Hcns Hphi s; rewrite <- Hcns; apply Hphi. Qed.

#[export] Instance globally_logically_equivalent_satisfies s :
  Proper (globally_logically_equivalent ==> iff) (satisfies s).
Proof.
  intros phi psi; rewrite globally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance globally_logically_equivalent_valid :
  Proper (globally_logically_equivalent ==> iff) valid.
Proof. by intros phi psi Heqv; unfold valid; setoid_rewrite Heqv. Qed.

Definition local_semantic_consequence (phi psi : Pattern) : Prop :=
  forall s e, esatisfies s e phi -> esatisfies s e psi.

Definition locally_logically_equivalent (phi psi : Pattern) : Prop :=
  forall s e, esatisfies s e phi <-> esatisfies s e psi.

Lemma locally_logically_equivalent_iff phi psi :
  locally_logically_equivalent phi psi
    <->
  local_semantic_consequence phi psi /\ local_semantic_consequence psi phi.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intro; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

#[export] Instance local_semantic_consequence_esatisfies s e :
  Proper (local_semantic_consequence ==> Basics.impl) (esatisfies s e).
Proof. intros phi psi Hcns Hphi; apply Hcns, Hphi. Qed.

#[export] Instance local_semantic_consequence_valid :
  Proper (local_semantic_consequence ==> Basics.impl) valid.
Proof. by intros phi psi Hcns Hphi s e; apply Hcns, Hphi. Qed.

#[export] Instance locally_logically_equivalent_satisfies s e :
  Proper (locally_logically_equivalent ==> iff) (esatisfies s e).
Proof.
  intros phi psi; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance locally_logically_equivalent_valid :
  Proper (locally_logically_equivalent ==> iff) valid.
Proof.
  intros phi psi; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Definition strong_semantic_consequence (phi psi : Pattern) : Prop :=
  forall s e, pattern_valuation s e phi ⊆ pattern_valuation s e psi.

Definition strongly_logically_equivalent (phi psi : Pattern) : Prop :=
  forall s e, pattern_valuation s e phi ≡ pattern_valuation s e psi.

Lemma strongly_logically_equivalent_iff phi psi :
  strongly_logically_equivalent phi psi
    <->
  strong_semantic_consequence phi psi /\ strong_semantic_consequence psi phi.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intros s e a; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

Lemma strong_semantic_consequence_valid phi psi :
  strong_semantic_consequence phi psi <-> valid (PImpl phi psi).
Proof.
  by unfold valid, satisfies; setoid_rewrite esatisfies_impl_classic.
Qed.

Lemma strongly_logically_equivalent_valid phi psi :
  strongly_logically_equivalent phi psi <-> valid (pIff phi psi).
Proof.
  rewrite valid_iff_alt_classic, <- !strong_semantic_consequence_valid.
  apply strongly_logically_equivalent_iff.
Qed.

#[export] Instance strong_semantic_consequence_valid_classic :
  Proper (strong_semantic_consequence ==> Basics.impl) valid.
Proof.
  intros phi psi; rewrite strong_semantic_consequence_valid.
  by unfold Basics.impl; apply valid_mp_classic.
Qed.

#[export] Instance strongly_logically_equivalent_valid_alt_classic :
  Proper (strongly_logically_equivalent ==> iff) valid.
Proof.
  intros phi psi; rewrite strongly_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma strong_semantic_consequence_local phi psi :
  strong_semantic_consequence phi psi -> local_semantic_consequence phi psi.
Proof.
  intros Hstrong s e; setoid_rewrite elem_of_equiv_top; intros Hphi a.
  by apply Hstrong, Hphi.
Qed.

Lemma local_semantic_consequence_global phi psi :
  local_semantic_consequence phi psi -> global_semantic_consequence phi psi.
Proof. by intros Hlocal s Hphi e; apply Hlocal, Hphi. Qed.

Lemma strongly_logically_equivalent_locally phi psi :
  strongly_logically_equivalent phi psi -> locally_logically_equivalent phi psi.
Proof.
  rewrite strongly_logically_equivalent_iff, locally_logically_equivalent_iff.
  by intros []; split; apply strong_semantic_consequence_local.
Qed.

Lemma locally_logically_equivalent_global phi psi :
  locally_logically_equivalent phi psi -> globally_logically_equivalent phi psi.
Proof.
  rewrite locally_logically_equivalent_iff, globally_logically_equivalent_iff.
  by intros []; split; apply local_semantic_consequence_global.
Qed.

Lemma locally_logically_equivalent_evar x y :
  locally_logically_equivalent (PEVar x) (PEVar y).
Proof. by intros s e; rewrite !esatisfies_evar. Qed.

Lemma globally_logically_equivalent_evar x y :
  globally_logically_equivalent (PEVar x) (PEVar y).
Proof.
  by apply locally_logically_equivalent_global, locally_logically_equivalent_evar.
Qed.

Lemma locally_logically_equivalent_not_strong :
  exists phi psi, locally_logically_equivalent phi psi /\ ~ strong_semantic_consequence phi psi.
Proof.
  assert (exists x y : EVar, x <> y) as (x & y & Hxy).
  {
    pose (x := fresh [] : EVar ).
    exists x, (fresh [x]).
    intro Hx.
    by apply infinite_is_fresh with [x], elem_of_list_singleton.
  }
  exists (PEVar x), (PEVar y); split.
  - by apply locally_logically_equivalent_evar.
  - intro Hlocal.
    pose (s := {| idomain := EVar; non_empty := populate x;
                  iapp := fun x y z => False; isigma := fun x y => False |}).
    assert (exists (e : Valuation s), ¬ pattern_valuation s e (PEVar x) ⊆  pattern_valuation s e (PEVar y))
      as (e & Hne).
    {
      unshelve esplit; [split; [exact id | exact (const ∅)] |].
      cbn; contradict Hxy.
      pose (pow_set_semiset s).
      by eapply @elem_of_singleton, Hxy, elem_of_singleton.
    }
    by contradict Hne; apply Hlocal.
Qed.

Lemma local_semantic_consequence_not_strong :
  exists phi psi, local_semantic_consequence phi psi /\ ~ strong_semantic_consequence phi psi.
Proof.
  destruct locally_logically_equivalent_not_strong as (phi & psi & Heqv & Hncons).
  by exists phi, psi; split; [apply locally_logically_equivalent_iff in Heqv as [] |].
Qed.

Lemma locally_logically_equivalent_not_strongly :
  exists phi psi, locally_logically_equivalent phi psi /\ ~ strongly_logically_equivalent phi psi.
Proof.
  destruct locally_logically_equivalent_not_strong as (phi & psi & Heqv & Hncons).
  exists phi, psi; split; [done |].
  by contradict Hncons; apply strongly_logically_equivalent_iff in Hncons as [].
Qed.

Context `{Set_ Pattern PatternSet}.

Definition set_esatisfies (s : Structure) (e : Valuation s) (Gamma : PatternSet) :=
  forall phi, phi ∈ Gamma -> esatisfies s e phi.

#[export] Instance set_esatisfies_proper (s : Structure) (e : Valuation s) :
  Proper ((≡) ==> (iff)) (set_esatisfies s e).
Proof.
  intros Gamma Gamma' Heqv.
  by split; intros Hall phi Hphi; apply Hall, Heqv.
Qed.

#[export] Instance set_esatisfies_proper_subseteq (s : Structure) (e : Valuation s) :
  Proper ((⊆) --> Basics.impl) (set_esatisfies s e).
Proof. by intros Gamma Gamma' Heqv Hall phi Hphi; apply Hall, Heqv. Qed.

Lemma set_esatisfies_singleton s e phi :
  set_esatisfies s e {[phi]} <-> esatisfies s e phi.
Proof.
  unfold set_esatisfies; setoid_rewrite elem_of_singleton.
  by split; [intros Hsat| intros Hsat _phi ->]; apply Hsat.
Qed.

Definition set_satisfies (s : Structure) (Gamma : PatternSet) :=
  forall e, set_esatisfies s e Gamma.

#[export] Instance set_satisfies_proper (s : Structure) :
  Proper ((≡) ==> (iff)) (set_satisfies s).
Proof.
  intros Gamma Gamma' Heqv.
  by split; intros Hall e phi Hphi; apply Hall, Heqv.
Qed.

#[export] Instance set_satisfies_proper_subseteq (s : Structure) :
  Proper ((⊆) --> Basics.impl) (set_satisfies s).
Proof. by intros Gamma Gamma' Heqv Hall e phi Hphi; apply Hall, Heqv. Qed.

Lemma set_satisfies_singleton s phi :
  set_satisfies s {[phi]} <-> satisfies s phi.
Proof.
  by unfold set_satisfies; setoid_rewrite set_esatisfies_singleton.
Qed.

Definition set_global_semantic_consequence (Gamma : PatternSet) (phi : Pattern) :=
  forall s, set_satisfies s Gamma -> satisfies s phi.

#[export] Instance set_global_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_global_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _phi phi ->.
  by unfold set_global_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_global_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_global_semantic_consequence.
Proof.
  intros Gamma Gamma' Hsub _phi phi -> HGamma' s HGamma.
  by apply HGamma'; rewrite Hsub.
Qed.

Lemma set_global_semantic_consequence_singleton phi psi :
  set_global_semantic_consequence {[phi]} psi <-> global_semantic_consequence phi psi.
Proof.
  unfold set_global_semantic_consequence, global_semantic_consequence.
  by setoid_rewrite set_satisfies_singleton.
Qed.

Lemma set_global_semantic_consequence_empty_valid phi :
  set_global_semantic_consequence ∅ phi <-> valid phi.
Proof.
  unfold set_global_semantic_consequence, valid.
  apply forall_proper; intro s; split; [| done].
  intro Hempty; apply Hempty; intros e _phi H_phi.
  contradict H_phi; apply not_elem_of_empty.
Qed.

Lemma set_global_semantic_consequence_union_left Gamma Gamma' phi :
  set_global_semantic_consequence Gamma phi ->
  set_global_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_l Gamma Gamma'). Qed.

Lemma set_global_semantic_consequence_union_right Gamma Gamma' phi :
  set_global_semantic_consequence Gamma' phi ->
  set_global_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_r Gamma Gamma'). Qed.

Lemma valid_set_global_semantic_consequence_any phi Gamma :
  valid phi -> set_global_semantic_consequence Gamma phi.
Proof.
  intro; rewrite <- (empty_subseteq Gamma).
  by apply set_global_semantic_consequence_empty_valid.
Qed.

#[export] Instance global_semantic_consequence_set_consequence Gamma :
  Proper (global_semantic_consequence ==> Basics.impl) (set_global_semantic_consequence Gamma).
Proof. by intros phi psi Hcns Hphi s HGamma; apply Hcns, Hphi. Qed.

#[export] Instance globally_logically_equivalent_set_consequence Gamma :
  Proper (globally_logically_equivalent ==> iff) (set_global_semantic_consequence Gamma).
Proof.
  intros phi psi; rewrite globally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_global_semantic_consequence_and Gamma phi psi :
  set_global_semantic_consequence Gamma (pAnd phi psi)
    <->
  set_global_semantic_consequence Gamma phi /\ set_global_semantic_consequence Gamma psi.
Proof.
  unfold set_global_semantic_consequence.
  setoid_rewrite satisfies_and_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_global_semantic_consequence_iff Gamma phi psi :
  set_global_semantic_consequence Gamma (pIff phi psi)
    <->
  set_global_semantic_consequence Gamma (PImpl phi psi)
    /\
  set_global_semantic_consequence Gamma (PImpl psi phi).
Proof.
  unfold set_global_semantic_consequence; setoid_rewrite satisfies_iff_alt_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Definition set_global_semantic_consequence_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure), set_satisfies s Gamma -> set_satisfies s Delta.

#[export] Instance set_global_semantic_consequence_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_global_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_global_semantic_consequence_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_global_semantic_consequence_set_proper_subseteq :
  Proper ((⊆) ==> (⊆) --> Basics.impl) set_global_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_global_semantic_consequence_set.
  by setoid_rewrite <- HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_global_semantic_consequence_set_satisfies_proper s :
  Proper (set_global_semantic_consequence_set ==> Basics.impl) (set_satisfies s).
Proof. by intros Gamma Delta HGammaDelta HGamma; apply HGammaDelta. Qed.

Definition set_globally_logically_equivalent_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure), set_satisfies s Gamma <-> set_satisfies s Delta.

#[export] Instance set_globally_logically_equivalent_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_globally_logically_equivalent_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_globally_logically_equivalent_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

Lemma set_globally_logically_equivalent_set_proper_iff Gamma Delta :
  set_globally_logically_equivalent_set Gamma Delta
    <->
  set_global_semantic_consequence_set Gamma Delta /\ set_global_semantic_consequence_set Delta Gamma .
Proof.
  unfold set_globally_logically_equivalent_set, set_global_semantic_consequence_set.
  by split; [intros Heqv; split; intros; apply Heqv | intros []; split; auto].
Qed.

#[export] Instance set_globally_logically_equivalent_set_set_satisfies_proper s :
  Proper (set_globally_logically_equivalent_set ==> iff) (set_satisfies s).
Proof.
  intros Gamma Delta HGammaDelta.
  apply set_globally_logically_equivalent_set_proper_iff in HGammaDelta as [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance set_global_semantic_consequence_set_consequence_proper :
  Proper (set_global_semantic_consequence_set --> globally_logically_equivalent ==> Basics.impl)
    set_global_semantic_consequence.
Proof.
  intros Delta Gamma HDelta phi psi Hphipsi Hphi s HGamma.
  by rewrite <- Hphipsi; apply Hphi; rewrite HDelta.
Qed.

#[export] Instance set_globally_logically_equivalent_set_consequence_proper :
  Proper (set_globally_logically_equivalent_set ==> globally_logically_equivalent ==> iff)
    set_global_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv phi psi Heqv; unfold set_global_semantic_consequence.
  by setoid_rewrite Hset_eqv; setoid_rewrite Heqv.
Qed.

Lemma set_globally_logically_equivalent_set_finite_classic
  `{!Elements Pattern PatternSet} `{!FinSet Pattern PatternSet} (Gamma : PatternSet) :
  set_globally_logically_equivalent_set Gamma {[finite_conjunction (elements Gamma)]}.
Proof.
  intro s.
  rewrite set_satisfies_singleton, satisfies_finite_conjunction_classic, Forall_forall.
  unfold set_satisfies, set_esatisfies, satisfies.
  setoid_rewrite elem_of_elements.
  itauto.
Qed.

Definition set_local_semantic_consequence (Gamma : PatternSet) (phi : Pattern) :=
  forall s e, set_esatisfies s e Gamma -> esatisfies s e phi.

#[export] Instance set_local_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_local_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _phi phi ->.
  by unfold set_local_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_local_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_local_semantic_consequence.
Proof.
  intros Gamma Gamma' Hsub _phi phi -> HGamma' s e HGamma.
  by apply HGamma'; rewrite Hsub.
Qed.

Lemma set_local_semantic_consequence_singleton phi psi :
  set_local_semantic_consequence {[phi]} psi <-> local_semantic_consequence phi psi.
Proof.
  unfold set_local_semantic_consequence, local_semantic_consequence.
  by setoid_rewrite set_esatisfies_singleton.
Qed.

Lemma set_local_semantic_consequence_empty_valid phi :
  set_local_semantic_consequence ∅ phi <-> valid phi.
Proof.
  unfold set_local_semantic_consequence, valid.
  apply forall_proper; intro s; split; [| done].
  intros Hempty e; apply Hempty; intros _phi H_phi.
  contradict H_phi; apply not_elem_of_empty.
Qed.

Lemma set_local_semantic_consequence_union_left Gamma Gamma' phi :
  set_local_semantic_consequence Gamma phi ->
  set_local_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_l Gamma Gamma'). Qed.

Lemma set_local_semantic_consequence_union_right Gamma Gamma' phi :
  set_local_semantic_consequence Gamma' phi ->
  set_local_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_r Gamma Gamma'). Qed.

Lemma valid_set_local_semantic_consequence_any phi Gamma :
  valid phi -> set_local_semantic_consequence Gamma phi.
Proof.
  intro; rewrite <- (empty_subseteq Gamma).
  by apply set_local_semantic_consequence_empty_valid.
Qed.

#[export] Instance local_semantic_consequence_set_consequence Gamma :
  Proper (local_semantic_consequence ==> Basics.impl) (set_local_semantic_consequence Gamma).
Proof. by intros phi psi Hcns Hphi s e HGamma; apply Hcns, Hphi. Qed.

#[export] Instance locally_logically_equivalent_set_consequence Gamma :
  Proper (locally_logically_equivalent ==> iff) (set_local_semantic_consequence Gamma).
Proof.
  intros phi psi; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_local_semantic_consequence_and Gamma phi psi :
  set_local_semantic_consequence Gamma (pAnd phi psi)
    <->
  set_local_semantic_consequence Gamma phi /\ set_local_semantic_consequence Gamma psi.
Proof.
  unfold set_local_semantic_consequence.
  setoid_rewrite esatisfies_and_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_local_semantic_consequence_iff Gamma phi psi :
  set_local_semantic_consequence Gamma (pIff phi psi)
    <->
  set_local_semantic_consequence Gamma (PImpl phi psi)
    /\
  set_local_semantic_consequence Gamma (PImpl psi phi).
Proof.
  unfold set_local_semantic_consequence; setoid_rewrite esatisfies_iff_alt_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Definition set_local_semantic_consequence_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation s), set_esatisfies s e Gamma -> set_esatisfies s e Delta.

#[export] Instance set_local_semantic_consequence_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_local_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_local_semantic_consequence_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_local_semantic_consequence_set_proper_subseteq :
  Proper ((⊆) ==> (⊆) --> Basics.impl) set_local_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_local_semantic_consequence_set.
  by setoid_rewrite <- HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_local_semantic_consequence_set_satisfies_proper s e :
  Proper (set_local_semantic_consequence_set ==> Basics.impl) (set_esatisfies s e).
Proof. by intros Gamma Delta HGammaDelta HGamma; apply HGammaDelta. Qed.

Definition set_locally_logically_equivalent_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation s),
    set_esatisfies s e Gamma <-> set_esatisfies s e Delta.

#[export] Instance set_locally_logically_equivalent_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_locally_logically_equivalent_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_locally_logically_equivalent_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

Lemma set_locally_logically_equivalent_set_proper_iff Gamma Delta :
  set_locally_logically_equivalent_set Gamma Delta
    <->
  set_local_semantic_consequence_set Gamma Delta /\ set_local_semantic_consequence_set Delta Gamma .
Proof.
  unfold set_locally_logically_equivalent_set, set_local_semantic_consequence_set.
  by split; [intros Heqv; split; intros; apply Heqv | intros []; split; auto].
Qed.

#[export] Instance set_locally_logically_equivalent_set_set_satisfies_proper s e :
  Proper (set_locally_logically_equivalent_set ==> iff) (set_esatisfies s e).
Proof.
  intros Gamma Delta HGammaDelta.
  apply set_locally_logically_equivalent_set_proper_iff in HGammaDelta as [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance set_local_semantic_consequence_set_consequence_proper :
  Proper (set_local_semantic_consequence_set --> locally_logically_equivalent ==> Basics.impl)
    set_local_semantic_consequence.
Proof.
  intros Delta Gamma HDelta phi psi Hphipsi Hphi s e HGamma.
  by rewrite <- Hphipsi; apply Hphi; rewrite HDelta.
Qed.

#[export] Instance set_locally_logically_equivalent_set_consequence_proper :
  Proper (set_locally_logically_equivalent_set ==> locally_logically_equivalent ==> iff)
    set_local_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv phi psi Heqv; unfold set_local_semantic_consequence.
  by setoid_rewrite Hset_eqv; setoid_rewrite Heqv.
Qed.

Lemma set_locally_logically_equivalent_set_finite_classic
  `{!Elements Pattern PatternSet} `{!FinSet Pattern PatternSet} (Gamma : PatternSet) :
  set_locally_logically_equivalent_set Gamma {[finite_conjunction (elements Gamma)]}.
Proof.
  intros s e.
  rewrite set_esatisfies_singleton, esatisfies_finite_conjunction_classic, Forall_forall.
  unfold set_esatisfies, esatisfies.
  setoid_rewrite elem_of_elements.
  itauto.
Qed.

Definition set_pattern_valuation
  (s : Structure) (e : Valuation s) (Gamma : PatternSet) : Ensemble idomain :=
    filtered_intersection s (.∈ Gamma ) (pattern_valuation s e).

Lemma elem_of_set_pattern_valuation s e Gamma a :
  a ∈ set_pattern_valuation s e Gamma
    <->
  forall phi, phi ∈ Gamma -> a ∈ pattern_valuation s e phi.
Proof. by apply elem_of_filtered_intersection. Qed.

#[export] Instance set_pattern_valuation_proper s e :
  Proper ((≡) ==> (≡)) (set_pattern_valuation s e).
Proof.
  intros Gamma Delta Heqv a; rewrite !elem_of_set_pattern_valuation.
  by setoid_rewrite Heqv.
Qed.

#[export] Instance set_pattern_valuation_proper_subseteq s e :
  Proper ((⊆) --> (⊆)) (set_pattern_valuation s e).
Proof.
  intros Gamma Delta Hsub a; rewrite !elem_of_set_pattern_valuation.
  by intros HGamma phi Hphi; apply HGamma, Hsub.
Qed.

Lemma set_pattern_valuation_empty_top s e : set_pattern_valuation s e ∅ ≡ top s.
Proof. apply filtered_intersection_empty_top, not_elem_of_empty. Qed.

Lemma set_pattern_valuation_singleton s e phi :
  set_pattern_valuation s e {[phi]} ≡ pattern_valuation s e phi.
Proof.
  unfold set_pattern_valuation; intro a; rewrite elem_of_filtered_intersection.
  setoid_rewrite elem_of_singleton.
  by firstorder congruence.
Qed.

Lemma top_set_pattern_valuation s e Gamma :
  set_pattern_valuation s e Gamma ≡ top s
    <->
  forall phi, phi ∈ Gamma -> pattern_valuation s e phi ≡ top s.
Proof.
  setoid_rewrite elem_of_equiv_top.
  setoid_rewrite elem_of_set_pattern_valuation.
  itauto.
Qed.

Lemma set_esatisfies_set_pattern_valuation s e Gamma :
  set_esatisfies s e Gamma <-> set_pattern_valuation s e Gamma ≡ top s.
Proof. by rewrite top_set_pattern_valuation. Qed.

Definition set_strong_semantic_consequence (Gamma : PatternSet) (phi : Pattern) :=
  forall s e, set_pattern_valuation s e Gamma ⊆ pattern_valuation s e phi.

#[export] Instance set_strong_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_strong_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _phi phi ->.
  by unfold set_strong_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_strong_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_strong_semantic_consequence.
Proof. by intros Gamma Gamma' Hsub _phi phi -> HGamma' s e; rewrite <- Hsub. Qed.

Lemma set_strong_semantic_consequence_singleton phi psi :
  set_strong_semantic_consequence {[phi]} psi <-> strong_semantic_consequence phi psi.
Proof.
  by unfold set_strong_semantic_consequence; setoid_rewrite set_pattern_valuation_singleton.
Qed.

Lemma set_strong_semantic_consequence_empty_valid phi :
  set_strong_semantic_consequence ∅ phi <-> valid phi.
Proof.
  unfold set_strong_semantic_consequence; setoid_rewrite set_pattern_valuation_empty_top.
  by setoid_rewrite top_subseteq_equiv.
Qed.

Lemma set_strong_semantic_consequence_union_left Gamma Gamma' phi :
  set_strong_semantic_consequence Gamma phi ->
  set_strong_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_l Gamma Gamma'). Qed.

Lemma set_strong_semantic_consequence_union_right Gamma Gamma' phi :
  set_strong_semantic_consequence Gamma' phi ->
  set_strong_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_r Gamma Gamma'). Qed.

Lemma valid_set_strong_semantic_consequence_any phi Gamma :
  valid phi -> set_strong_semantic_consequence Gamma phi.
Proof.
  intro; rewrite <- (empty_subseteq Gamma).
  by apply set_strong_semantic_consequence_empty_valid.
Qed.

#[export] Instance strong_semantic_consequence_set_consequence Gamma :
  Proper (strong_semantic_consequence ==> Basics.impl) (set_strong_semantic_consequence Gamma).
Proof. by intros phi psi Hcns Hphi s e a HGamma; apply Hcns, Hphi. Qed.

#[export] Instance strongly_logically_equivalent_set_consequence Gamma :
  Proper (strongly_logically_equivalent ==> iff) (set_strong_semantic_consequence Gamma).
Proof.
  intros phi psi; rewrite strongly_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_strong_semantic_consequence_and Gamma phi psi :
  set_strong_semantic_consequence Gamma (pAnd phi psi)
    <->
  set_strong_semantic_consequence Gamma phi /\ set_strong_semantic_consequence Gamma psi.
Proof.
  unfold set_strong_semantic_consequence.
  setoid_rewrite pattern_valuation_and_classic; [| done].
  unfold subseteq, set_subseteq_instance.
  setoid_rewrite elem_of_intersection.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_strong_semantic_consequence_iff Gamma phi psi :
  set_strong_semantic_consequence Gamma (pIff phi psi)
    <->
  set_strong_semantic_consequence Gamma (PImpl phi psi)
    /\
  set_strong_semantic_consequence Gamma (PImpl psi phi).
Proof. by unfold pIff; rewrite set_strong_semantic_consequence_and. Qed.

Definition set_strong_semantic_consequence_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation s),
    set_pattern_valuation s e Gamma ⊆ set_pattern_valuation s e Delta.

#[export] Instance set_strong_semantic_consequence_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_strong_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_strong_semantic_consequence_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_strong_semantic_consequence_set_proper_subseteq :
  Proper ((⊆) ==> (⊆) --> Basics.impl) set_strong_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_strong_semantic_consequence_set.
  by setoid_rewrite <- HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_strong_semantic_consequence_set_satisfies_proper s e :
  Proper (set_strong_semantic_consequence_set ==> Basics.impl) (set_esatisfies s e).
Proof.
  intros Gamma Delta HGammaDelta.
  rewrite !set_esatisfies_set_pattern_valuation, !elem_of_equiv_top.
  by intros HGamma a; apply HGammaDelta, HGamma.
Qed.

Definition set_strongly_logically_equivalent_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation s),
    set_pattern_valuation s e Gamma ≡ set_pattern_valuation s e Delta.

#[export] Instance set_strongly_logically_equivalent_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_strongly_logically_equivalent_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_strongly_logically_equivalent_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

Lemma set_strongly_logically_equivalent_set_proper_iff Gamma Delta :
  set_strongly_logically_equivalent_set Gamma Delta
    <->
  set_strong_semantic_consequence_set Gamma Delta /\ set_strong_semantic_consequence_set Delta Gamma .
Proof.
  unfold set_strongly_logically_equivalent_set, set_strong_semantic_consequence_set.
  setoid_rewrite set_equiv_subseteq.
  by split; [intros Heqv; split; intros; apply Heqv | intros []; split; auto].
Qed.

#[export] Instance set_strongly_logically_equivalent_set_set_satisfies_proper s e :
  Proper (set_strongly_logically_equivalent_set ==> iff) (set_esatisfies s e).
Proof.
  intros Gamma Delta HGammaDelta.
  apply set_strongly_logically_equivalent_set_proper_iff in HGammaDelta as [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance set_strong_semantic_consequence_set_consequence_proper :
  Proper (set_strong_semantic_consequence_set --> strongly_logically_equivalent ==> Basics.impl)
    set_strong_semantic_consequence.
Proof.
  intros Delta Gamma HDelta phi psi Hphipsi Hphi s e a HGamma.
  by apply Hphipsi, Hphi, HDelta.
Qed.

#[export] Instance set_strongly_logically_equivalent_set_consequence_proper :
  Proper (set_strongly_logically_equivalent_set ==> strongly_logically_equivalent ==> iff)
    set_strong_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv phi psi Heqv.
  do 3 (apply forall_proper; intro).
  by split; intros Hsat ?; apply Heqv, Hsat, Hset_eqv.
Qed.

Lemma set_strongly_logically_equivalent_set_finite_classic
    `{!Elements Pattern PatternSet} `{!FinSet Pattern PatternSet} (Gamma : PatternSet) :
  set_strongly_logically_equivalent_set Gamma {[finite_conjunction (elements Gamma)]}.
Proof.
  intros s e.
  rewrite set_pattern_valuation_singleton, pattern_valuation_finite_conjunction_classic
    by done.
  intro a; rewrite elem_of_set_pattern_valuation, elem_of_intersection_list.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_elements.
  split.
  - by intros Hall _X (phi & -> & Hphi); apply Hall.
  - by intros Hall phi Hphi; apply Hall; eexists.
Qed.


Lemma set_strong_semantic_consequence_local Gamma phi :
  set_strong_semantic_consequence Gamma phi -> set_local_semantic_consequence Gamma phi.
Proof.
  intros Hstrong s e; rewrite set_esatisfies_set_pattern_valuation; setoid_rewrite elem_of_equiv_top.
  by intros HGamma a; apply Hstrong, HGamma.
Qed.

Lemma set_local_semantic_consequence_global Gamma phi :
  set_local_semantic_consequence Gamma phi -> set_global_semantic_consequence Gamma phi.
Proof. by intros Hlocal s Hphi e; apply Hlocal, Hphi. Qed.

Record ClosedPattern (phi : Pattern) : Prop :=
{
  cpe : FEV phi ≡ ∅;
  cps : FSV phi ≡ ∅;
}.

Lemma ClosedPattern_FV_equal phi s e1 e2 :
  ClosedPattern phi -> FV_equal s e1 e2 phi.
Proof.
  intros []; split; intros x Hx; exfalso.
  - eapply (@not_elem_of_empty EVar EVarSet); [typeclasses eauto |].
    by rewrite <- cpe0; apply EVarFree_FEV.
  - eapply (@not_elem_of_empty SVar SVarSet); [typeclasses eauto |].
    by rewrite <- cps0; apply SVarFree_FSV.
Qed.

Lemma pattern_valuation_closed_pattern s e1 e2 phi :
  ClosedPattern phi -> pattern_valuation s e1 phi ≡ pattern_valuation s e2 phi.
Proof. by intro; apply pattern_valuation_fv, ClosedPattern_FV_equal. Qed.

Lemma esatisfies_closed_pattern s e1 e2 phi :
  ClosedPattern phi -> esatisfies s e1 phi <-> esatisfies s e2 phi.
Proof.
  by intros; unfold esatisfies; rewrite pattern_valuation_closed_pattern.
Qed.

Lemma satistifes_closed_pattern s phi :
  ClosedPattern phi -> satisfies s phi <-> exists e, esatisfies s e phi.
Proof.
  split; [intros Hsat; exists inhabitant; apply Hsat |].
  by intros [e He] e'; eapply esatisfies_closed_pattern.
Qed.

Definition set_closed_pattern (Gamma : PatternSet) : Prop :=
  forall phi, phi ∈ Gamma -> ClosedPattern phi.

Lemma set_esatisfies_closed_pattern s e1 e2 Gamma :
  set_closed_pattern Gamma -> set_esatisfies s e1 Gamma <-> set_esatisfies s e2 Gamma.
Proof.
  intro HGamma; apply forall_proper; intro phi; unfold esatisfies.
  by split; intros Hsat Hphi;
    (rewrite pattern_valuation_closed_pattern; [by apply Hsat |]);
    apply HGamma.
Qed.

Lemma set_satistifes_closed_pattern s Gamma :
  set_closed_pattern Gamma -> set_satisfies s Gamma <-> exists e, set_esatisfies s e Gamma.
Proof.
  split; [intros Hsat; exists inhabitant; apply Hsat |].
  by intros [e He] e'; eapply set_esatisfies_closed_pattern.
Qed.

Lemma set_local_semantic_consequence_global_closed_pattern Gamma phi :
  set_closed_pattern Gamma ->
    set_local_semantic_consequence Gamma phi
      <->
    set_global_semantic_consequence Gamma phi.
Proof.
  split; [by apply set_local_semantic_consequence_global |].
  intros Hglobal s e HGamma; apply Hglobal.
  by apply set_satistifes_closed_pattern; [| eexists].
Qed.

Inductive CrispSet
  (s : Structure) (A : Ensemble idomain) : Prop :=
| cs_empty : A ≡ ∅ -> CrispSet s A
| cs_top : A ≡ top s -> CrispSet s A.

Definition spredicate (s : Structure) (phi : Pattern) : Prop :=
  forall (e : Valuation s), CrispSet s (pattern_valuation s e phi).

Definition predicate (phi : Pattern) : Prop :=
  forall s : Structure, spredicate s phi.

Class BotClosed (P : Pattern -> Prop) :=
{
  bot_closed : P (PBot)
}.

Class TopClosed (P : Pattern -> Prop) :=
{
  top_closed : P (pTop)
}.

Class NegClosed (P : Pattern -> Prop) :=
{
  neg_closed : forall phi, P phi -> P (pNeg phi)
}.

Class ImplClosed (P : Pattern -> Prop) :=
{
  impl_closed : forall phi psi, P phi -> P psi -> P (PImpl phi psi)
}.

Class AndClosed (P : Pattern -> Prop) :=
{
  and_closed : forall phi psi, P phi -> P psi -> P (pAnd phi psi)
}.

Class OrClosed (P : Pattern -> Prop) :=
{
  or_closed : forall phi psi, P phi -> P psi -> P (pOr phi psi)
}.

Class IffClosed (P : Pattern -> Prop) :=
{
  iff_closed : forall phi psi, P phi -> P psi -> P (pIff phi psi)
}.

Class FiniteConjunctionClosed (P : Pattern -> Prop) :=
{
  finite_conjunction_closed :
    forall phis, Forall P phis -> P (finite_conjunction phis)
}.

Class FiniteDisjunctionClosed (P : Pattern -> Prop) :=
{
  finite_disjunction_closed :
    forall phis, Forall P phis -> P (finite_disjunction phis)
}.

Class ExClosed (P : Pattern -> Prop) :=
{
  ex_closed : forall x phi, P phi -> P (PEx x phi)
}.

Class AllClosed (P : Pattern -> Prop) :=
{
  all_closed : forall x phi, P phi -> P (pAll x phi)
}.

Class MuClosed (P : Pattern -> Prop) :=
{
  mu_closed : forall X phi, OccursPositively X phi -> P phi -> P (PMu X phi)
}.

Class NuClosed (P : Pattern -> Prop) :=
{
  nu_closed : forall X phi, OccursPositively X phi -> P phi -> P (pNu X phi)
}.


#[export] Instance spredicate_bot s : BotClosed (spredicate s).
Proof. by constructor; intro e; constructor 1. Qed.

#[export] Instance spredicate_impl s : ImplClosed (spredicate s).
Proof.
  constructor; intros phi psi Hphi Hpsi e.
  destruct (Hphi e) as [Hphib | Hphit];
    [by right; apply esatisfies_impl_classic; rewrite Hphib; apply empty_subseteq |].
  destruct (Hpsi e) as [Hpsib | Hpsit];
    [| by right; apply esatisfies_impl_classic; rewrite Hpsit].
  left. rewrite pattern_valuation_impl_alt_classic, Hphit, Hpsib by done.
  apply elem_of_equiv_empty; intros x; rewrite elem_of_union, elem_of_complement.
  by unfold top; cbn; intros [].
Qed.

#[export] Instance spredicate_ex_classic s : ExClosed (spredicate s).
Proof.
  constructor; intros x phi Hphi e.
  destruct (classic (exists v, pattern_valuation s (valuation_eupdate s e x v) phi ≡ top s))
    as [[v Hv] | Hnv].
  - by right; apply esatisfies_ex_elim; eexists.
  - left; cbn; apply empty_indexed_union; intro a.
    eapply not_ex_all_not with (n := a) in Hnv.
    by destruct (Hphi (valuation_eupdate s e x a)).
Qed.

Section sec_pattern_closure_properties.

Context
  (P : Pattern -> Prop)
  `{BotClosed P}
  `{ImplClosed P}.

#[export] Instance closed_neg : NegClosed P.
Proof. by constructor; intros phi Hphi; apply impl_closed; [| apply bot_closed]. Qed.

#[export] Instance closed_top : TopClosed P.
Proof. by constructor; apply neg_closed, bot_closed. Qed.

#[export] Instance closed_or : OrClosed P.
Proof. by constructor; intros phi psi Hphi Hpsi; apply impl_closed; [apply neg_closed |]. Qed.

#[export] Instance closed_and : AndClosed P.
Proof.
  by constructor; intros phi psi Hphi Hpsi; apply neg_closed, or_closed; apply neg_closed.
Qed.

#[export] Instance closed_iff : IffClosed P.
Proof. by constructor; intros phi psi Hphi Hpsi; apply and_closed; apply impl_closed. Qed.

#[export] Instance closed_finite_conjunction : FiniteConjunctionClosed P.
Proof.
  by constructor; intros phis; induction 1;
    [apply top_closed | apply and_closed].
Qed.

#[export] Instance closed_finite_disjunction : FiniteDisjunctionClosed P.
Proof.
  by constructor; intros phis; induction 1;
    [apply bot_closed | apply or_closed].
Qed.

#[export] Instance closed_all `{ExClosed P} : AllClosed P.
Proof. by constructor; intros x phi Hphi; apply neg_closed, ex_closed, neg_closed. Qed.

End sec_pattern_closure_properties.

#[export] Instance predicate_bot : BotClosed predicate.
Proof. by constructor; intro s; apply bot_closed. Qed.

#[export] Instance predicate_impl : ImplClosed predicate.
Proof.
  by constructor; intros phi psi Hphi Hpsi s; apply impl_closed;
    [apply Hphi | apply Hpsi].
Qed.

#[export] Instance predicate_ex : ExClosed predicate.
Proof. by constructor; intros x phi Hphi s; apply ex_closed, Hphi. Qed.

#[export] Instance closed_pattern_bot : BotClosed ClosedPattern.
Proof. by constructor; constructor. Qed.

#[export] Instance closed_pattern_impl : ImplClosed ClosedPattern.
Proof.
  by constructor; intros phi psi [] []; constructor; cbn; set_solver.
Qed.

#[export] Instance closed_pattern_ex : ExClosed ClosedPattern.
Proof.
  by constructor; intros x phi []; constructor; cbn; set_solver.
Qed.

#[export] Instance closed_pattern_mu : MuClosed ClosedPattern.
Proof.
  by constructor; intros x phi Hpos []; constructor; cbn; set_solver.
Qed.

Record ClosedPredicate (phi : Pattern) : Prop :=
{
  cp_closed_pattern :> ClosedPattern phi;
  cp_predicate : predicate phi
}.

#[export] Instance closed_predicate_bot : BotClosed ClosedPredicate.
Proof. by constructor; split; apply bot_closed. Qed.

#[export] Instance closed_predicate_impl : ImplClosed ClosedPredicate.
Proof. by constructor; intros phi psi [] []; split; apply impl_closed. Qed.

#[export] Instance closed_predicate_ex : ExClosed ClosedPredicate.
Proof. by constructor; intros x phi []; split; apply ex_closed. Qed.

Definition set_closed_predicate (Gamma : PatternSet) : Prop :=
  forall phi, phi ∈ Gamma -> ClosedPredicate phi.

Lemma set_pattern_valuation_closed_predicate_crisp_classic Gamma s e :
  set_closed_predicate Gamma ->
  CrispSet s (set_pattern_valuation s e Gamma).
Proof.
  intros HGamma.
  destruct (classic (set_pattern_valuation s e Gamma ≡ top s)) as [| Hval];
    [by right | left].
  apply elem_of_equiv_empty; intro a; contradict Hval.
  apply top_filtered_intersection; intros phi Hphi.
  rewrite elem_of_set_pattern_valuation in Hval.
  specialize (Hval _ Hphi).
  destruct (HGamma _ Hphi); destruct (cp_predicate0 s e) as [Heqv |]; [| done].
  by rewrite Heqv in Hval.
Qed.

Lemma set_closed_predicate_pattern Gamma :
  set_closed_predicate Gamma -> set_closed_pattern Gamma.
Proof. by intros Hpreds phi Hphi; apply Hpreds. Qed.

Lemma set_local_semantic_consequence_global_closed_predicate Gamma phi :
  set_closed_predicate Gamma ->
    set_local_semantic_consequence Gamma phi
      <->
    set_global_semantic_consequence Gamma phi.
Proof.
  by intro HGamma; apply set_local_semantic_consequence_global_closed_pattern,
    set_closed_predicate_pattern.
Qed.

Lemma set_strong_semantic_consequence_local_closed_predicate Gamma phi :
  set_closed_predicate Gamma ->
    set_strong_semantic_consequence Gamma phi
      <->
    set_local_semantic_consequence Gamma phi.
Proof.
  intro HGamma; split; [by apply set_strong_semantic_consequence_local |].
  intros Hlocal s e a Ha.
  destruct (set_pattern_valuation_closed_predicate_crisp_classic Gamma s e HGamma) as
    [Hrew | Htop]; [by rewrite Hrew in Ha |].
  by apply Hlocal; [apply set_esatisfies_set_pattern_valuation |].
Qed.

Definition Tautology (phi : Pattern) : Prop :=
  forall s F,  @PropositionalPatternValuation s F -> F phi ≡ top s.

Lemma tautology_valid phi : Tautology phi -> valid phi.
Proof. by intros Htauto s e; apply Htauto. Qed.

Lemma tautology_phi_iff_phi phi : Tautology (pIff phi phi).
Proof. by intros s F ?; apply top_pattern_valuation_iff_classic. Qed.

Lemma tautology_phi_or_phi_iff_phi phi : Tautology (pIff (pOr phi phi) phi).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_phi_iff_phi_and_phi phi : Tautology (pIff phi (pAnd phi phi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_or_comm phi psi : Tautology (pIff (pOr phi psi) (pOr psi phi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_and_comm phi psi : Tautology (pIff (pAnd phi psi) (pAnd psi phi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_phi_impl_phi_or_psi phi psi : Tautology (PImpl phi (pOr phi psi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_phi_and_psi_impl_phi phi psi : Tautology (PImpl (pAnd phi psi) phi).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_bot_impl_phi phi : Tautology (PImpl PBot phi).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, ppv_bot by done.
  by set_solver.
Qed.

Lemma tautology_excluded_middle phi : Tautology (pOr phi (pNeg phi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_or_classic, pattern_valuation_neg_classic by done.
  rewrite elem_of_equiv_top; intro a; rewrite elem_of_union, elem_of_complement.
  by apply classic.
Qed.

Lemma tautology_impl_impl_and phi psi chi :
  Tautology (pIff (PImpl phi (PImpl psi chi)) (PImpl (pAnd phi psi) chi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_impl_alt_classic,
    pattern_valuation_and_classic by done.
  rewrite complement_intersection_classic.
  by set_solver.
Qed.

Lemma tautology_impl_impl_comm phi psi chi :
  Tautology (pIff (PImpl phi (PImpl psi chi)) (PImpl psi (PImpl phi chi))).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_impl_alt_classic
    by done.
  by set_solver.
Qed.

Definition evaluates_to_singleton (s : Structure) (e : Valuation s) (phi : Pattern) : Prop :=
  exists a, pattern_valuation s e phi ≡ {[a]}.

Class always_evaluates_to_singleton (s : Structure) (phi : Pattern) : Prop :=
{
  aes : forall (e : Valuation s), evaluates_to_singleton s e phi
}.

#[export] Instance always_evaluates_to_singleton_evar s x :
  always_evaluates_to_singleton s (PEVar x).
Proof. by constructor; intros; eexists. Qed.

Definition singleton_value
  (s : Structure) (phi : Pattern) `{!always_evaluates_to_singleton s phi}
  (e : Valuation s) : { a : idomain | pattern_valuation s e phi ≡ {[a]} }.
Proof.
  destruct always_evaluates_to_singleton0.
  specialize (aes0 e).
  by apply constructive_indefinite_description in aes0.
Qed.

Lemma pattern_valuation_evar_sub0_not_free s e x delta phi c :
  ~ EVarFree x phi ->
  pattern_valuation s e (evar_sub0 x delta phi)
    ≡
  pattern_valuation s (valuation_eupdate s e x c) phi.
Proof.
  intro; rewrite evar_sub0_not_free by done.
  apply pattern_valuation_fv; split; [| done].
  intros y Hy; cbn; unfold fn_update.
  by case_decide; subst.
Qed.

Lemma pattern_valuation_evar_sub0 s e x delta phi
  `{!always_evaluates_to_singleton s delta} :
  EFreeFor x delta phi ->
  pattern_valuation s e (evar_sub0 x delta phi)
    ≡
  pattern_valuation s (valuation_eupdate s e x (` (singleton_value s delta e))) phi.
Proof.
  remember (proj1_sig _) as c.
  intros Hfree_for.
  destruct (classic (EVarFree x phi)) as [Hfree |];
    [| by apply pattern_valuation_evar_sub0_not_free].
  revert e c Heqc; induction phi; try (by inversion Hfree); intros ? c Hc.
  - by inversion Hfree; subst; cbn; unfold fn_update;
      rewrite !decide_True by done; destruct singleton_value.
  - rewrite pattern_valuation_impl_alt_classic by done.
    apply EFreeForImpl in Hfree_for as [Hfree_for1 Hfree_for2].
    destruct (classic (EVarFree x phi1)); [destruct (classic (EVarFree x phi2)) |].
    + rewrite <- IHphi1, <- IHphi2 by done.
      by apply pattern_valuation_impl_alt_classic.
    + rewrite <- IHphi1, <- pattern_valuation_evar_sub0_not_free
        with (phi := phi2) (delta := delta) by done.
      by apply pattern_valuation_impl_alt_classic.
    + inversion Hfree; [done | subst].
      rewrite <- IHphi2, <- pattern_valuation_evar_sub0_not_free
        with (phi := phi1) (delta := delta) by done.
      by apply pattern_valuation_impl_alt_classic.
  - apply EFreeForEx in Hfree_for as [Hfree_for1 Hx].
    inversion Hfree; subst y phi0.
    cbn; rewrite decide_False by done; cbn.
    intro a; rewrite !elem_of_indexed_union.
    setoid_rewrite IHphi; [| done..].
    apply exist_proper; intro b.
    rewrite valuation_eupdate_comm by done.
    subst; destruct (singleton_value s delta e0) as [c Hc].
    destruct (singleton_value s delta (valuation_eupdate s e0 e b)) as [d Hd]; cbn.
    rewrite pattern_valuation_fv, Hc in Hd;
      [by apply singleton_equiv_inj in Hd; subst |].
    split; cbn; [| done]; intros; unfold fn_update.
    case_decide; [| done].
    by subst; exfalso; apply Hx.
  - apply EFreeForMu in Hfree_for as [Hfree_for1 Hx].
    inversion Hfree; subst; cbn.
    intro a; rewrite !elem_of_filtered_intersection.
    setoid_rewrite IHphi; [| done..].
    setoid_rewrite valuation_esupdate_comm.
    apply forall_proper; intro A.
    destruct (singleton_value s delta e) as [c Hc].
    destruct (singleton_value s delta (valuation_supdate s e s0 A)) as [d Hd]; cbn.
    rewrite pattern_valuation_fv, Hc in Hd;
      [by apply singleton_equiv_inj in Hd; subst |].
    split; cbn; [done |]; intros; unfold fn_update.
    case_decide; [| done].
    by subst; exfalso; apply Hx.
  - cbn.
    apply EFreeForApp in Hfree_for as [Hfree_for1 Hfree_for2].
    destruct (classic (EVarFree x phi1)); [destruct (classic (EVarFree x phi2)) |].
    + by rewrite <- IHphi1, <- IHphi2.
    + by rewrite <- IHphi1, <- pattern_valuation_evar_sub0_not_free
        with (phi := phi2) (delta := delta).
    + inversion Hfree; [done | subst].
      by rewrite <- IHphi2, <- pattern_valuation_evar_sub0_not_free
        with (phi := phi1) (delta := delta).
Qed.

Lemma pattern_valuation_evar_sub0_evar s e x y phi :
  EFreeFor x (PEVar y) phi ->
  pattern_valuation s e (evar_sub0 x (PEVar y) phi)
    ≡
  pattern_valuation s (valuation_eupdate s e x (eval s e y)) phi.
Proof.
  intro Hfree_for.
  unshelve rewrite pattern_valuation_evar_sub0 by done;
    [typeclasses eauto |].
  destruct (singleton_value s (PEVar y) e); cbn in *.
  by apply singleton_equiv_inj in e0 as <-.
Qed.

Lemma valid_evar_sub0_rename_ex x y phi :
  EFreeFor x (PEVar y) phi ->
  valid (PImpl (evar_sub0 x (PEVar y) phi) (PEx x phi)).
Proof.
  intros ? ? ?; apply esatisfies_impl_classic.
  rewrite pattern_valuation_evar_sub0_evar by done; cbn.
  apply (member_of_indexed_union _ (λ a : idomain, pattern_valuation s (valuation_eupdate s e x a) phi)).
Qed.

Lemma valid_evar_sub0_rename_all x y phi :
  EFreeFor x (PEVar y) phi ->
  valid (PImpl (pAll x phi) (evar_sub0 x (PEVar y) phi)).
Proof.
  intros ? ? ?; rewrite esatisfies_impl_classic, pattern_valuation_forall_classic.
  rewrite pattern_valuation_evar_sub0_evar by done; cbn.
  apply (member_of_indexed_intersection _ (λ a : idomain, pattern_valuation s (valuation_eupdate s e x a) phi)).
Qed.

Lemma valid_evar_rename x y phi :
  ~ EOccurs y phi ->
  EFreeFor x (PEVar y) phi ->
  valid (pIff phi (evar_rename x y phi)).
Proof.
  intros Hy Hfree_for.
  destruct (decide (x = y));
    [by subst; rewrite evar_rename_id; apply tautology_valid, tautology_phi_iff_phi |].
  intros s e.
  apply esatisfies_iff_classic.
  revert e; induction phi; intro. 1-3, 8: done.
  - apply EFreeForImpl in Hfree_for as [].
    rewrite EOccurs_impl in Hy; apply not_or_and in Hy as [].
    by cbn; rewrite IHphi1, IHphi2.
  - rewrite EOccurs_ex in Hy; apply not_or_and in Hy as [? Hy].
    cbn; case_decide; cbn; intro a; rewrite !elem_of_indexed_union; apply exist_proper; intro b;
      [| by rewrite IHphi; [done..| eapply EFreeForEx]].
    subst e.
    assert (EFreeFor x (PEVar y) (evar_rename x y phi))
      by (apply EFreeForInd_iff, evar_rename_FreeFor;
            [|rewrite <- EOccursInd_iff]; done).
    rewrite pattern_valuation_evar_sub0_evar by done.
    apply EFreeForEx in Hfree_for as [].
    rewrite <- IHphi, valuation_eupdate_eq by done.
    apply pattern_valuation_fv; destruct e0; split; cbn; [| done].
    intros z Hz; unfold fn_update; case_decide; [done |].
    case_decide; [| done].
    by subst; contradict Hy; left.
  - cbn; intro a; rewrite !elem_of_filtered_intersection; apply forall_proper; intro A.
    rewrite EOccurs_mu in Hy.
    by rewrite IHphi; [..| eapply EFreeForMu].
  - apply EFreeForApp in Hfree_for as [].
    rewrite EOccurs_app in Hy; apply not_or_and in Hy as [].
    by cbn; rewrite IHphi1, IHphi2.
Qed.

Lemma valid_evar_sub_rename x y phi :
  valid (PImpl (esubst phi x (PEVar y)) (PEx x phi)).
Proof.
  unfold esubst, SV, EV; cbn.
  replace (elements (BSV phi ∩ _)) with (@nil SVar)
    by (symmetry; apply elements_empty_iff; set_solver).
  cbn; destruct (decide (EVarBound y phi)); cycle 1.
  - replace (elements _) with (@nil EVar).
    + cbn; apply valid_evar_sub0_rename_ex.
      by apply EFreeFor_x_y_if_not_bound.
    + symmetry; apply elements_empty_iff, elem_of_equiv_empty; intro.
      rewrite elem_of_intersection, elem_of_union, elem_of_singleton, <- EVarBound_BEV.
      by intros [? [|Hempty]]; [subst | contradict Hempty; apply not_elem_of_empty].
  - replace (elements _) with [y]; cycle 1.
    {
      apply Permutation_singleton_l.
      rewrite <- elements_singleton.
      apply elements_proper.
      intro a; rewrite elem_of_intersection, elem_of_union, !elem_of_singleton.
      rewrite <- EVarBound_BEV.
      split; [by intros ->; split; [| left] | intros [? [-> | Hempty]]]; [done |].
      contradict Hempty; apply not_elem_of_empty.
    }
    cbn.

(*
Lemma pattern_valuation_nu_classic e X phi :
  pattern_valuation e (pNu X phi)
    ≡
  filtered_union (fun B => B ⊆ pattern_valuation (valuation_supdate e X B) phi) id.
Proof.
  unfold pNu.
  rewrite pattern_valuation_neg_classic; cbn.
  rewrite complement_filtered_intersection_classic.
  intro x; rewrite !elem_of_filtered_union; cbn.
  split; intros (A & HA & Hx); exists (complement A); split;
    [| done | | by rewrite complement_twice_classic]; clear x Hx; intros x; rewrite elem_of_complement.
  - intro Hna.
*)
