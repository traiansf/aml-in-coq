From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude fin_sets.
From AML Require Import Signature Pattern.

Section sec_variables.

Context
  `{signature}.

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
  split; [intros [He Hs] | intros [[He Hs] Hy]]; repeat split.
  - by intros; eapply He; [| apply sp_ex].
  - by intros; eapply Hs; [| apply sp_ex].
  - by intros; eapply He; [| apply sp_refl].
  - by inversion 2; subst; [apply Hy | eapply He].
  - by inversion 2; subst; eapply Hs.
Qed.

Lemma EFreeForMu x delta y phi :
  EFreeFor x delta (PMu y phi) <-> EFreeFor x delta phi /\ (SVarFree y delta -> ~ EVarFree x phi).
Proof.
  split; [intros [He Hs] | intros [[He Hs] Hy]]; repeat split.
  - by intros; eapply He; [| apply sp_mu].
  - by intros; eapply Hs; [| apply sp_mu].
  - by intros; eapply Hs; [| apply sp_refl].
  - by inversion 2; subst; eapply He.
  - by inversion 2; subst; [apply Hy | eapply Hs].
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

Lemma EFreeFor_x_theta_if_not_bound x theta phi :
  (forall y, EVarFree y theta -> ~ EVarBound y phi) ->
  (forall y, SVarFree y theta -> ~ SVarBound y phi) ->
  EFreeFor x theta phi.
Proof.
  intros Hetheta Hstheta; split; intros z Hz theta' Htheta'; exfalso.
  - by eapply Hetheta; [| eapply EVarBound_BEV, SubPatternExBound].
  - by eapply Hstheta; [| eapply SVarBound_BSV, SubPatternMuBound].
Qed.

Lemma EFreeFor_x_theta_if_no_free_vars x theta phi :
  FEV theta ≡ ∅ ->
  FSV theta ≡ ∅ ->
  EFreeFor x theta phi.
Proof.
  intros Hetheta Hstheta; apply EFreeFor_x_theta_if_not_bound.
  - by intro; rewrite EVarFree_FEV, Hetheta; set_solver.
  - by intro; rewrite SVarFree_FSV, Hstheta; set_solver.
Qed.

Lemma EFreeFor_x_y_if_not_bound x y phi (Hx : ~ EVarBound y phi) : EFreeFor x (PEVar y) phi.
Proof. by apply EFreeFor_x_theta_if_not_bound; inversion 1. Qed.

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

Record ClosedPattern (phi : Pattern) : Prop :=
{
  cpe : forall x, ~ EVarFree x phi;
  cps : forall X, ~ SVarFree X phi;
}.

Definition set_closed_pattern `{Set_ Pattern PatternSet} (Gamma : PatternSet) : Prop :=
  forall phi, phi ∈ Gamma -> ClosedPattern phi.

End sec_variables.
