From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude fin_sets.
From AML Require Import Signature Pattern.

Section sec_variables.

Context
  `{signature}.

Inductive EVarFree (x : EVar) : Pattern -> Prop :=
| ef_evar : EVarFree x (PEVar x)
| ef_impl_left : forall ϕ ψ, EVarFree x ϕ -> EVarFree x (PImpl ϕ ψ)
| ef_impl_right : forall ϕ ψ, EVarFree x ψ -> EVarFree x (PImpl ϕ ψ)
| ef_app_left : forall ϕ ψ, EVarFree x ϕ -> EVarFree x (PApp ϕ ψ)
| ef_app_right : forall ϕ ψ, EVarFree x ψ -> EVarFree x (PApp ϕ ψ)
| ef_mu : forall X ϕ, EVarFree x ϕ -> EVarFree x (μₚ X ϕ)
| ef_ex : forall y ϕ, EVarFree x ϕ -> y <> x -> EVarFree x (PEx y ϕ)
.

Inductive EVarBound (x : EVar) : Pattern -> Prop :=
| eb_impl_left : forall ϕ ψ, EVarBound x ϕ -> EVarBound x (PImpl ϕ ψ)
| eb_impl_right : forall ϕ ψ, EVarBound x ψ -> EVarBound x (PImpl ϕ ψ)
| eb_app_left : forall ϕ ψ, EVarBound x ϕ -> EVarBound x (PApp ϕ ψ)
| eb_app_right : forall ϕ ψ, EVarBound x ψ -> EVarBound x (PApp ϕ ψ)
| eb_mu : forall X ϕ, EVarBound x ϕ -> EVarBound x (μₚ X ϕ)
| eb_ex_eq : forall ϕ, EVarBound x (PEx x ϕ)
| eb_ex_neq : forall y ϕ, EVarBound x ϕ -> EVarBound x (PEx y ϕ)
.

Inductive SVarFree (x : SVar) : Pattern -> Prop :=
| sf_svar : SVarFree x (PSVar x)
| sf_impl_left : forall ϕ ψ, SVarFree x ϕ -> SVarFree x (PImpl ϕ ψ)
| sf_impl_right : forall ϕ ψ, SVarFree x ψ -> SVarFree x (PImpl ϕ ψ)
| sf_app_left : forall ϕ ψ, SVarFree x ϕ -> SVarFree x (PApp ϕ ψ)
| sf_app_right : forall ϕ ψ, SVarFree x ψ -> SVarFree x (PApp ϕ ψ)
| sf_ex : forall X ϕ, SVarFree x ϕ -> SVarFree x (PEx X ϕ)
| sf_mu : forall y ϕ, SVarFree x ϕ -> y <> x -> SVarFree x (μₚ y ϕ)
.

Inductive SVarBound (x : SVar) : Pattern -> Prop :=
| sb_impl_left : forall ϕ ψ, SVarBound x ϕ -> SVarBound x (PImpl ϕ ψ)
| sb_impl_right : forall ϕ ψ, SVarBound x ψ -> SVarBound x (PImpl ϕ ψ)
| sb_app_left : forall ϕ ψ, SVarBound x ϕ -> SVarBound x (PApp ϕ ψ)
| sb_app_right : forall ϕ ψ, SVarBound x ψ -> SVarBound x (PApp ϕ ψ)
| sb_ex : forall X ϕ, SVarBound x ϕ -> SVarBound x (PEx X ϕ)
| sb_mu_eq : forall ϕ, SVarBound x (μₚ x ϕ)
| sb_mu_neq : forall y ϕ, SVarBound x ϕ -> SVarBound x (μₚ y ϕ)
.

Fixpoint FEV (p : Pattern) : EVarSet :=
match p with
| PEVar x => {[x]}
| PSVar X => ∅
| POp _ => ∅
| PImpl ϕ ψ => FEV ϕ ∪ FEV ψ
| PApp ϕ ψ => FEV ϕ ∪ FEV ψ
| PEx x ϕ => FEV ϕ ∖ {[x]}
| μₚ X ϕ => FEV ϕ
end.

Lemma EVarFree_FEV : forall x p,
EVarFree x p <-> x ∈ FEV p.
Proof.
induction p; cbn.
- by rewrite elem_of_singleton; split; inversion 1; constructor.
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
| POp _ => ∅
| PImpl ϕ ψ => FSV ϕ ∪ FSV ψ
| PApp ϕ ψ => FSV ϕ ∪ FSV ψ
| μₚ x ϕ => FSV ϕ ∖ {[x]}
| PEx X ϕ => FSV ϕ
end.

Lemma SVarFree_FSV : forall x p,
SVarFree x p <-> x ∈ FSV p.
Proof.
induction p; cbn.
- by split; [inversion 1 | intro Hx; contradict Hx; apply not_elem_of_empty].
- by rewrite elem_of_singleton; split; inversion 1; constructor.
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
| POp _ => ∅
| PImpl ϕ ψ => BEV ϕ ∪ BEV ψ
| PApp ϕ ψ => BEV ϕ ∪ BEV ψ
| PEx x ϕ => BEV ϕ ∪ {[x]}
| μₚ X ϕ => BEV ϕ
end.

Lemma EVarBound_BEV : forall x p,
EVarBound x p <-> x ∈ BEV p.
Proof.
induction p; cbn.
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

Lemma EOccurs_impl x ϕ1 ϕ2 :
EOccurs x (PImpl ϕ1 ϕ2) <-> EOccurs x ϕ1 \/ EOccurs x ϕ2.
Proof.
rewrite EV_Eoccurs; unfold EV; cbn; rewrite! elem_of_union; unfold EOccurs.
rewrite !EVarFree_FEV, !EVarBound_BEV.
itauto.
Qed.

Lemma EOccurs_app x ϕ1 ϕ2 :
EOccurs x (PApp ϕ1 ϕ2) <-> EOccurs x ϕ1 \/ EOccurs x ϕ2.
Proof.
rewrite EV_Eoccurs; unfold EV; cbn; rewrite! elem_of_union.
unfold EOccurs; rewrite !EVarFree_FEV, !EVarBound_BEV.
itauto.
Qed.

Lemma EOccurs_ex x y ϕ :
EOccurs x (PEx y ϕ) <-> x = y \/ EOccurs x ϕ.
Proof.
rewrite EV_Eoccurs; unfold EV; cbn.
rewrite! elem_of_union, elem_of_difference, elem_of_singleton.
unfold EOccurs; rewrite !EVarFree_FEV, !EVarBound_BEV.
destruct (decide (x = y)); itauto.
Qed.

Lemma EOccurs_mu x Y ϕ :
EOccurs x (μₚ Y ϕ) <-> EOccurs x ϕ.
Proof.
rewrite EV_Eoccurs; unfold EV; cbn.
rewrite! elem_of_union.
unfold EOccurs; rewrite !EVarFree_FEV, !EVarBound_BEV.
itauto.
Qed.

Inductive EOccursInd (x : EVar) : Pattern -> Prop :=
| eo_evar : EOccursInd x (PEVar x)
| eo_impl_left : forall ϕ1 ϕ2, EOccursInd x ϕ1 -> EOccursInd x (PImpl ϕ1 ϕ2)
| eo_impl_right : forall ϕ1 ϕ2, EOccursInd x ϕ2 -> EOccursInd x (PImpl ϕ1 ϕ2)
| eo_app_left : forall ϕ1 ϕ2, EOccursInd x ϕ1 -> EOccursInd x (PApp ϕ1 ϕ2)
| eo_app_right : forall ϕ1 ϕ2, EOccursInd x ϕ2 -> EOccursInd x (PApp ϕ1 ϕ2)
| eo_mu : forall Y ϕ, EOccursInd x ϕ -> EOccursInd x (μₚ Y ϕ)
| eo_ex_eq : forall ϕ, EOccursInd x (PEx x ϕ)
| eo_ex_neq : forall y ϕ, EOccursInd x ϕ -> EOccursInd x (PEx y ϕ).

Lemma EOccursInd_iff x ϕ : EOccurs x ϕ <-> EOccursInd x ϕ.
Proof.
induction ϕ.
2,7: by split; [intros [Hx | Hx]; inversion Hx | inversion 1].
- by split; [intros [Hx | Hx]; inversion Hx | inversion 1; left ]; constructor.
- rewrite EOccurs_impl, IHϕ1, IHϕ2.
  by split; [intros []; constructor | inversion 1]; itauto.
- rewrite EOccurs_ex, IHϕ.
  split; [intros []; [subst; apply eo_ex_eq | apply eo_ex_neq] | inversion 1];
    itauto.
- rewrite EOccurs_mu, IHϕ.
  by split; [constructor | inversion 1].
- rewrite EOccurs_app, IHϕ1, IHϕ2.
  by split; [intros []; constructor | inversion 1]; itauto.
Qed.

Fixpoint BSV (p : Pattern) : SVarSet :=
match p with
| PEVar _ => ∅
| PSVar _ => ∅
| POp _ => ∅
| PImpl ϕ ψ => BSV ϕ ∪ BSV ψ
| PApp ϕ ψ => BSV ϕ ∪ BSV ψ
| μₚ x ϕ => BSV ϕ ∪ {[x]}
| PEx X ϕ => BSV ϕ
end.

Lemma SVarBound_BSV : forall x p,
SVarBound x p <-> x ∈ BSV p.
Proof.
induction p; cbn.
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

Lemma SOccurs_impl x ϕ1 ϕ2 :
SOccurs x (PImpl ϕ1 ϕ2) <-> SOccurs x ϕ1 \/ SOccurs x ϕ2.
Proof.
rewrite SV_Soccurs; unfold SV; cbn; rewrite! elem_of_union; unfold SOccurs.
rewrite !SVarFree_FSV, !SVarBound_BSV.
itauto.
Qed.

Lemma SOccurs_app x ϕ1 ϕ2 :
SOccurs x (PApp ϕ1 ϕ2) <-> SOccurs x ϕ1 \/ SOccurs x ϕ2.
Proof.
rewrite SV_Soccurs; unfold SV; cbn; rewrite! elem_of_union.
unfold SOccurs; rewrite !SVarFree_FSV, !SVarBound_BSV.
itauto.
Qed.

Lemma SOccurs_mu x y ϕ :
SOccurs x (μₚ y ϕ) <-> x = y \/ SOccurs x ϕ.
Proof.
rewrite SV_Soccurs; unfold SV; cbn.
rewrite! elem_of_union, elem_of_difference, elem_of_singleton.
unfold SOccurs; rewrite !SVarFree_FSV, !SVarBound_BSV.
destruct (decide (x = y)); itauto.
Qed.

Lemma SOccurs_ex x Y ϕ :
SOccurs x (PEx Y ϕ) <-> SOccurs x ϕ.
Proof.
rewrite SV_Soccurs; unfold SV; cbn.
rewrite! elem_of_union.
unfold SOccurs; rewrite !SVarFree_FSV, !SVarBound_BSV.
itauto.
Qed.

Inductive SOccursInd (x : SVar) : Pattern -> Prop :=
| so_svar : SOccursInd x (PSVar x)
| so_impl_left : forall ϕ1 ϕ2, SOccursInd x ϕ1 -> SOccursInd x (PImpl ϕ1 ϕ2)
| so_impl_right : forall ϕ1 ϕ2, SOccursInd x ϕ2 -> SOccursInd x (PImpl ϕ1 ϕ2)
| so_app_left : forall ϕ1 ϕ2, SOccursInd x ϕ1 -> SOccursInd x (PApp ϕ1 ϕ2)
| so_app_right : forall ϕ1 ϕ2, SOccursInd x ϕ2 -> SOccursInd x (PApp ϕ1 ϕ2)
| so_ex : forall Y ϕ, SOccursInd x ϕ -> SOccursInd x (PEx Y ϕ)
| so_mu_eq : forall ϕ, SOccursInd x (μₚ x ϕ)
| so_mu_neq : forall y ϕ, SOccursInd x ϕ -> SOccursInd x (μₚ y ϕ).

Lemma SOccursInd_iff x ϕ : SOccurs x ϕ <-> SOccursInd x ϕ.
Proof.
induction ϕ.
1,7: by split; [intros [Hx | Hx]; inversion Hx | inversion 1].
- by split; [intros [Hx | Hx]; inversion Hx | inversion 1; left ]; constructor.
- rewrite SOccurs_impl, IHϕ1, IHϕ2.
  by split; [intros []; constructor | inversion 1]; itauto.
- rewrite SOccurs_ex, IHϕ.
  by split; [constructor | inversion 1].
- rewrite SOccurs_mu, IHϕ.
  split; [intros []; [subst; apply so_mu_eq | apply so_mu_neq] | inversion 1];
    itauto.
- rewrite SOccurs_app, IHϕ1, IHϕ2.
  by split; [intros []; constructor | inversion 1]; itauto.
Qed.

Lemma SubPatternExBound z theta ϕ : SubPattern (PEx z theta) ϕ -> z ∈ BEV ϕ.
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

Lemma SubPatternMuBound z theta ϕ : SubPattern (μₚ z theta) ϕ -> z ∈ BSV ϕ.
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

Record EFreeFor (x : EVar) (delta ϕ : Pattern) :=
{
  eff_evar : forall z, EVarFree z delta -> z <> x ->
    forall theta, SubPattern (PEx z theta) ϕ -> ~ EVarFree x theta;
  eff_svar : forall z, SVarFree z delta ->
    forall theta, SubPattern (μₚ z theta) ϕ -> ~ EVarFree x theta
}.

Lemma EFreeForAtomic x delta a : PatternAtomic a -> EFreeFor x delta a.
Proof. by inversion 1; (split; [inversion 3 | inversion 2]). Qed.

Lemma EFreeForImpl x delta ϕ1 ϕ2 :
  EFreeFor x delta (PImpl ϕ1 ϕ2) <-> EFreeFor x delta ϕ1 /\ EFreeFor x delta ϕ2.
Proof.
  split; [intros [He Hs] | intros [[He1 Hs1] [He2 Hs2]]];
    [split |]; (split; intros z Hz; [intros Hxz|]; intros theta Hsub).
  - by eapply He; [..| apply sp_impl_left].
  - by eapply Hs; [| apply sp_impl_left].
  - by eapply He; [..| apply sp_impl_right].
  - by eapply Hs; [| apply sp_impl_right].
  - by inversion_clear Hsub; [eapply He1 | eapply He2].
  - by inversion_clear Hsub; [eapply Hs1 | eapply Hs2].
Qed.

Lemma EFreeForApp x delta ϕ1 ϕ2 :
  EFreeFor x delta (PApp ϕ1 ϕ2) <-> EFreeFor x delta ϕ1 /\ EFreeFor x delta ϕ2.
Proof.
  split; [intros [He Hs] | intros [[He1 Hs1] [He2 Hs2]]];
    [split |]; (split; intros z Hz; [intros Hxz|]; intros theta Hsub).
  - by eapply He; [..| apply sp_app_left].
  - by eapply Hs; [| apply sp_app_left].
  - by eapply He; [..| apply sp_app_right].
  - by eapply Hs; [| apply sp_app_right].
  - by inversion_clear Hsub; [eapply He1 | eapply He2].
  - by inversion_clear Hsub; [eapply Hs1 | eapply Hs2].
Qed.

Lemma EFreeForEx x delta y ϕ :
  EFreeFor x delta (PEx y ϕ) <-> EFreeFor x delta ϕ /\ (EVarFree y delta -> x <> y -> ~ EVarFree x ϕ).
Proof.
  split; [intros [He Hs] | intros [[He Hs] Hy]]; repeat split.
  - by intros; eapply He; [..| apply sp_ex].
  - by intros; eapply Hs; [| apply sp_ex].
  - by intros; eapply He; [.. | apply sp_refl].
  - by inversion 3; subst; [apply Hy | eapply He].
  - by inversion 2; subst; eapply Hs.
Qed.

Lemma EFreeForMu x delta y ϕ :
  EFreeFor x delta (μₚ y ϕ) <-> EFreeFor x delta ϕ /\ (SVarFree y delta -> ~ EVarFree x ϕ).
Proof.
  split; [intros [He Hs] | intros [[He Hs] Hy]]; repeat split.
  - by intros; eapply He; [..| apply sp_mu].
  - by intros; eapply Hs; [| apply sp_mu].
  - by intros; eapply Hs; [| apply sp_refl].
  - by inversion 3; subst; eapply He.
  - by inversion 2; subst; [apply Hy | eapply Hs].
Qed.

Inductive EFreeForInd (x : EVar) (delta : Pattern) : Pattern -> Prop :=
| effi_evar : forall y, EFreeForInd x delta (PEVar y)
| effi_svar : forall Y, EFreeForInd x delta (PSVar Y)
| effi_op : forall o, EFreeForInd x delta (POp o)
| effi_impl : forall ϕ1 ϕ2, EFreeForInd x delta ϕ1 -> EFreeForInd x delta ϕ2 ->
    EFreeForInd x delta (PImpl ϕ1 ϕ2)
| effi_app : forall ϕ1 ϕ2, EFreeForInd x delta ϕ1 -> EFreeForInd x delta ϕ2 ->
    EFreeForInd x delta (PApp ϕ1 ϕ2)
| effi_ex : forall y ϕ, EFreeForInd x delta ϕ -> (EVarFree y delta -> x <> y -> ~ EVarFree x ϕ) ->
    EFreeForInd x delta (PEx y ϕ)
| effi_mu : forall Y ϕ, EFreeForInd x delta ϕ -> (SVarFree Y delta -> ~ EVarFree x ϕ) ->
    EFreeForInd x delta (μₚ Y ϕ).

Lemma EFreeForInd_iff x delta ϕ : EFreeFor x delta ϕ <-> EFreeForInd x delta ϕ.
Proof.
  induction ϕ.
  1-2,7: by split; [constructor |split; [inversion 3 | inversion 2]].
  - rewrite EFreeForImpl, IHϕ1, IHϕ2.
    by split; [by intros []; constructor | inversion 1].
  - rewrite EFreeForEx, IHϕ.
    by split; [by intros []; constructor | inversion 1].
  - rewrite EFreeForMu, IHϕ.
    by split; [by intros []; constructor | inversion 1].
  - rewrite EFreeForApp, IHϕ1, IHϕ2.
    by split; [by intros []; constructor | inversion 1].
Qed.

Lemma EFreeForInd_x_not_occurs x delta ϕ (Hx : ~ EOccursInd x ϕ) : EFreeForInd x delta ϕ.
Proof.
  induction ϕ; cycle 4. 3-5 : by constructor.
  - constructor; [by apply IHϕ; contradict Hx; constructor |].
    by intros _; contradict Hx; constructor; apply EOccursInd_iff; left.
  - by constructor; [apply IHϕ1 | apply IHϕ2]; contradict Hx;
      [apply eo_app_left | apply eo_app_right].
  - by constructor; [apply IHϕ1 | apply IHϕ2]; contradict Hx;
      [apply eo_impl_left | apply eo_impl_right].
  - constructor; [by apply IHϕ; contradict Hx; constructor |].
    by intros _ _; contradict Hx; constructor; apply EOccursInd_iff; left.
Qed.

Lemma EFreeFor_x_theta_if_not_bound x theta ϕ :
  (forall y, EVarFree y theta -> y <> x -> ~ EVarBound y ϕ) ->
  (forall y, SVarFree y theta -> ~ SVarBound y ϕ) ->
  EFreeFor x theta ϕ.
Proof.
  intros Hetheta Hstheta; (split; intros z Hz; [intros Hzx |]; intros theta' Htheta'); exfalso.
  - by eapply Hetheta; [..| eapply EVarBound_BEV, SubPatternExBound].
  - by eapply Hstheta; [| eapply SVarBound_BSV, SubPatternMuBound].
Qed.

Lemma EFreeFor_x_theta_if_no_free_vars x theta ϕ :
  FEV theta ⊆ {[x]} ->
  FSV theta ≡ ∅ ->
  EFreeFor x theta ϕ.
Proof.
  intros Hetheta Hstheta; apply EFreeFor_x_theta_if_not_bound.
  - by intros y Hy; apply EVarFree_FEV, Hetheta, elem_of_singleton in Hy.
  - by intro; rewrite SVarFree_FSV, Hstheta; set_solver.
Qed.

Lemma EFreeFor_x_y_if_not_bound x y ϕ (Hx : ~ EVarBound y ϕ) : EFreeFor x (PEVar y) ϕ.
Proof. by apply EFreeFor_x_theta_if_not_bound; inversion 1. Qed.

Record SFreeFor (x : SVar) (delta ϕ : Pattern) :=
{
  sff_evar : forall z, EVarFree z delta ->
    forall theta, SubPattern (PEx z theta) ϕ -> ~ SVarFree x theta;
  sff_svar : forall z, SVarFree z delta -> z <> x ->
    forall theta, SubPattern (μₚ z theta) ϕ -> ~ SVarFree x theta
}.

Lemma SFreeForAtomic x delta a : PatternAtomic a -> SFreeFor x delta a.
Proof. by inversion 1; (split; [inversion 2 | inversion 3]). Qed.

Lemma SFreeForImpl x delta ϕ1 ϕ2 :
  SFreeFor x delta (PImpl ϕ1 ϕ2) <-> SFreeFor x delta ϕ1 /\ SFreeFor x delta ϕ2.
Proof.
  split; [intros [He Hs] | intros [[He1 Hs1] [He2 Hs2]]];
    [split |]; (split; intros z Hz; [| intros Hxz]; intros theta Hsub).
  - by eapply He; [| apply sp_impl_left].
  - by eapply Hs; [..| apply sp_impl_left].
  - by eapply He; [| apply sp_impl_right].
  - by eapply Hs; [..| apply sp_impl_right].
  - by inversion_clear Hsub; [eapply He1 | eapply He2].
  - by inversion_clear Hsub; [eapply Hs1 | eapply Hs2].
Qed.

Lemma SFreeForApp x delta ϕ1 ϕ2 :
  SFreeFor x delta (PApp ϕ1 ϕ2) <-> SFreeFor x delta ϕ1 /\ SFreeFor x delta ϕ2.
Proof.
  split; [intros [He Hs] | intros [[He1 Hs1] [He2 Hs2]]];
    [split |]; (split; intros z Hz; [| intros Hxz]; intros theta Hsub).
  - by eapply He; [| apply sp_app_left].
  - by eapply Hs; [..| apply sp_app_left].
  - by eapply He; [| apply sp_app_right].
  - by eapply Hs; [..| apply sp_app_right].
  - by inversion_clear Hsub; [eapply He1 | eapply He2].
  - by inversion_clear Hsub; [eapply Hs1 | eapply Hs2].
Qed.

Lemma SFreeForEx x delta y ϕ :
  SFreeFor x delta (PEx y ϕ) <-> SFreeFor x delta ϕ /\ (EVarFree y delta -> ~ SVarFree x ϕ).
Proof.
  split; [intros [He Hs] | intros [[He Hs] Hy]]; repeat split.
  - by intros; eapply He; [| apply sp_ex].
  - by intros; eapply Hs; [..| apply sp_ex].
  - by intros; eapply He; [| apply sp_refl].
  - by inversion 2; subst; [apply Hy | eapply He].
  - by inversion 3; subst; eapply Hs.
Qed.

Lemma SFreeForMu x delta y ϕ :
  SFreeFor x delta (μₚ y ϕ) <-> SFreeFor x delta ϕ /\ (SVarFree y delta -> y <> x -> ~ SVarFree x ϕ).
Proof.
  split; [intros [He Hs] | intros [[He Hs] Hy]]; repeat split.
  - by intros; eapply He; [| apply sp_mu].
  - by intros; eapply Hs; [..| apply sp_mu].
  - by intros; eapply Hs; [..| apply sp_refl].
  - by inversion 2; subst; eapply He.
  - by inversion 3; subst; [apply Hy | eapply Hs].
Qed.

Inductive SFreeForInd (x : SVar) (delta : Pattern) : Pattern -> Prop :=
| sffi_evar : forall y, SFreeForInd x delta (PEVar y)
| sffi_svar : forall Y, SFreeForInd x delta (PSVar Y)
| sffi_op : forall o, SFreeForInd x delta (POp o)
| sffi_impl : forall ϕ1 ϕ2, SFreeForInd x delta ϕ1 -> SFreeForInd x delta ϕ2 ->
    SFreeForInd x delta (PImpl ϕ1 ϕ2)
| sffi_app : forall ϕ1 ϕ2, SFreeForInd x delta ϕ1 -> SFreeForInd x delta ϕ2 ->
    SFreeForInd x delta (PApp ϕ1 ϕ2)
| sffi_ex : forall y ϕ, SFreeForInd x delta ϕ -> (EVarFree y delta -> ~ SVarFree x ϕ) ->
    SFreeForInd x delta (PEx y ϕ)
| sffi_mu : forall Y ϕ, SFreeForInd x delta ϕ -> (SVarFree Y delta -> Y <> x -> ~ SVarFree x ϕ) ->
    SFreeForInd x delta (μₚ Y ϕ).

Lemma SFreeForInd_iff x delta ϕ : SFreeFor x delta ϕ <-> SFreeForInd x delta ϕ.
Proof.
  induction ϕ.
  1-2,7: by split; [constructor | split; [inversion 2 | inversion 3]].
  - rewrite SFreeForImpl, IHϕ1, IHϕ2.
    by split; [by intros []; constructor | inversion 1].
  - rewrite SFreeForEx, IHϕ.
    by split; [by intros []; constructor | inversion 1].
  - rewrite SFreeForMu, IHϕ.
    by split; [intros []; constructor | inversion 1].
  - rewrite SFreeForApp, IHϕ1, IHϕ2.
    by split; [by intros []; constructor | inversion 1].
Qed.

Lemma SFreeForInd_x_not_occurs x delta ϕ (Hx : ~ SOccursInd x ϕ) : SFreeForInd x delta ϕ.
Proof.
  induction ϕ; cycle 4. 3-5 : by constructor.
  - constructor; [by apply IHϕ; contradict Hx; constructor |].
    by intros _ _; contradict Hx; constructor; apply SOccursInd_iff; left.
  - by constructor; [apply IHϕ1 | apply IHϕ2]; contradict Hx;
      [apply so_app_left | apply so_app_right].
  - by constructor; [apply IHϕ1 | apply IHϕ2]; contradict Hx;
      [apply so_impl_left | apply so_impl_right].
  - constructor; [by apply IHϕ; contradict Hx; constructor |].
    by intros _; contradict Hx; constructor; apply SOccursInd_iff; left.
Qed.

Lemma SFreeFor_x_theta_if_not_bound x theta ϕ :
  (forall y, EVarFree y theta -> ~ EVarBound y ϕ) ->
  (forall y, SVarFree y theta -> y <> x -> ~ SVarBound y ϕ) ->
  SFreeFor x theta ϕ.
Proof.
  intros Hetheta Hstheta; (split; intros z Hz; [| intros Hxz]; intros theta' Htheta'); exfalso.
  - by eapply Hetheta; [| eapply EVarBound_BEV, SubPatternExBound].
  - by eapply Hstheta; [..| eapply SVarBound_BSV, SubPatternMuBound].
Qed.

Lemma SFreeFor_x_theta_if_no_free_vars x theta ϕ :
  FEV theta ≡ ∅ ->
  FSV theta ⊆ {[x]} ->
  SFreeFor x theta ϕ.
Proof.
  intros Hetheta Hstheta; apply SFreeFor_x_theta_if_not_bound.
  - by intro; rewrite EVarFree_FEV, Hetheta; set_solver.
  - by intros y Hy; apply SVarFree_FSV, Hstheta, elem_of_singleton in Hy.
Qed.

Lemma SFreeFor_x_y_if_not_bound x y ϕ (Hx : ~ SVarBound y ϕ) : SFreeFor x (PSVar y) ϕ.
Proof. by apply SFreeFor_x_theta_if_not_bound; inversion 1. Qed.

Inductive OccursPositively (X : SVar) : Pattern -> Prop :=
| op_evar : forall x, OccursPositively X (PEVar x)
| op_svar : forall Y, OccursPositively X (PSVar Y)
| op_cons : forall c, OccursPositively X (POp c)
| op_app : forall ϕ ψ, OccursPositively X ϕ -> OccursPositively X ψ ->
    OccursPositively X (PApp ϕ ψ)
| op_ex : forall x ϕ, OccursPositively X ϕ -> OccursPositively X (PEx x ϕ)
| op_mu_eq : forall ϕ, OccursPositively X (μₚ X ϕ)
| op_mu_neq : forall Y ϕ, Y <> X -> OccursPositively X ϕ ->
    OccursPositively X (μₚ Y ϕ)
| op_impl : forall ϕ ψ, OccursNegatively X ϕ -> OccursPositively X ψ ->
    OccursPositively X (PImpl ϕ ψ)
with OccursNegatively (X : SVar) : Pattern -> Prop :=
| on_evar : forall x, OccursNegatively X (PEVar x)
| on_svar : forall Y, Y <> X -> OccursNegatively X (PSVar Y)
| on_cons : forall c, OccursNegatively X (POp c)
| on_app : forall ϕ ψ, OccursNegatively X ϕ -> OccursNegatively X ψ ->
    OccursNegatively X (PApp ϕ ψ)
| on_ex : forall x ϕ, OccursNegatively X ϕ -> OccursNegatively X (PEx x ϕ)
| on_mu_eq : forall ϕ, OccursNegatively X (μₚ X ϕ)
| on_mu_neq : forall Y ϕ, Y <> X -> OccursNegatively X ϕ ->
    OccursNegatively X (μₚ Y ϕ)
| on_impl : forall ϕ ψ, OccursPositively X ϕ -> OccursNegatively X ψ ->
    OccursNegatively X (PImpl ϕ ψ)
.

Record ClosedPattern (ϕ : Pattern) : Prop :=
{
  cpe : forall x, ~ EVarFree x ϕ;
  cps : forall X, ~ SVarFree X ϕ;
}.

Definition set_closed_pattern `{Set_ Pattern PatternSet} (Gamma : PatternSet) : Prop :=
  forall ϕ, ϕ ∈ Gamma -> ClosedPattern ϕ.

Lemma ClosedPattern_iff ϕ :
  ClosedPattern ϕ <-> FEV ϕ ≡ ∅ /\ FSV ϕ ≡ ∅.
Proof.
  split; intros [HEV HSV]; cycle 1; split.
  - by intros x Hx; rewrite EVarFree_FEV, HEV in Hx; contradict Hx; apply not_elem_of_empty.
  - by intros x Hx; rewrite SVarFree_FSV, HSV in Hx; contradict Hx; apply not_elem_of_empty.
  - intro x; specialize (HEV x).
    rewrite EVarFree_FEV in HEV.
    by set_solver.
  - intro x; specialize (HSV x).
    rewrite SVarFree_FSV in HSV.
    by set_solver.
Qed.

Lemma ClosedPattern_elim ϕ :
  FEV ϕ ≡ ∅ -> FSV ϕ ≡ ∅ -> ClosedPattern ϕ.
Proof. by intros; apply ClosedPattern_iff. Qed.

Definition CFEV (c : AppContext) : EVarSet := FEV (csubst c pBot).

Lemma elem_of_CFEV x c : x ∈ CFEV c <-> forall ϕ, x ∈ FEV (csubst c ϕ).
Proof.
  split; [| by intros Hϕ; apply Hϕ].
  induction c; cbn; [intros Hx; contradict Hx; apply not_elem_of_empty |..];
    setoid_rewrite elem_of_union; intros [] ϕ.
  - by left; apply IHc.
  - by right.
  - by left.
  - by right; apply IHc.
Qed.

Inductive CEVarFree (x : EVar) : AppContext -> Prop :=
| cevf_ll : forall c p, CEVarFree x c -> CEVarFree x (LApp c p)
| cevf_lr : forall c p, EVarFree x p -> CEVarFree x (LApp c p)
| cevf_rr : forall c p, CEVarFree x c -> CEVarFree x (RApp p c)
| cevf_rl : forall c p, EVarFree x p -> CEVarFree x (RApp p c)
.

Lemma CEVarFree_CFEV x c : CEVarFree x c <-> x ∈ CFEV c.
Proof.
  induction c; cbn.
  - by split; [inversion 1 | intros Hx; contradict Hx; apply not_elem_of_empty].
  - rewrite elem_of_union, <- IHc.
    split; [inversion 1 | intros []]; subst.
    + by left.
    + by right; apply EVarFree_FEV.
    + by apply cevf_ll.
    + by apply cevf_lr; apply EVarFree_FEV.
  - rewrite elem_of_union, <- IHc.
    split; [inversion 1 | intros []]; subst.
    + by right.
    + by left; apply EVarFree_FEV.
    + by apply cevf_rl; apply EVarFree_FEV.
    + by apply cevf_rr.
Qed.

End sec_variables.
