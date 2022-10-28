From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Ensemble Structure.

Section sec_valuation.

Context
  `{s : Structure}.


Record Valuation : Type :=
{
  eval : EVar -> idomain;
  sval : SVar -> Ensemble idomain
}.

Record ValuationEquiv (v1 v2 : Valuation) : Prop :=
{
  veqve : forall x, eval v1 x = eval v2 x;
  veqvs : forall x, sval v1 x ≡ sval v2 x;
}.

#[export] Instance valuation_equiv : Equiv Valuation := ValuationEquiv.

#[export] Instance ValidationInhabited : Inhabited Valuation :=
  populate {| eval := const inhabitant; sval := const ∅ |}.

Definition valuation_eupdate (e : Valuation) (x : EVar) (a : idomain) : Valuation :=
{|
  eval := fn_update (eval e) x a;
  sval := sval e
|}.

#[export] Instance valuation_eupdate_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) valuation_eupdate.
Proof.
  intros e1 e2 [] _x x -> _a a ->.
  by split; [| done]; intro b; cbn; unfold fn_update; case_decide; [| apply veqve0].
Qed.

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

#[export] Instance valuation_supdate_proper : Proper ((≡) ==> (=) ==> (≡) ==> (≡)) valuation_supdate.
Proof.
  intros e1 e2 [] _x x -> A1 A2 Heqv.
  by split; [done |]; intro A; cbn; unfold fn_update; case_decide; [| apply veqvs0].
Qed.

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

Lemma valuation_supdate_twice e x a b :
  valuation_supdate (valuation_supdate e x a) x b
    ≡
  valuation_supdate e x b.
Proof. by split; [| intro; cbn; unfold fn_update; case_decide]. Qed.

Lemma valuation_esupdate_comm e x a y b :
  valuation_supdate (valuation_eupdate e x a) y b
    =
  valuation_eupdate (valuation_supdate e y b) x a.
Proof. by destruct e. Qed.

End sec_valuation.
