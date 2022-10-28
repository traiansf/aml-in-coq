From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.


Class BotClosed `{signature} (P : Pattern -> Prop) :=
{
  bot_closed : P pBot
}.

Class TopClosed `{signature} (P : Pattern -> Prop) :=
{
  top_closed : P pTop
}.

Class NegClosed `{signature} (P : Pattern -> Prop) :=
{
  neg_closed : forall phi, P phi -> P (pNeg phi)
}.

Class ImplClosed `{signature} (P : Pattern -> Prop) :=
{
  impl_closed : forall phi psi, P phi -> P psi -> P (PImpl phi psi)
}.

Class AndClosed `{signature} (P : Pattern -> Prop) :=
{
  and_closed : forall phi psi, P phi -> P psi -> P (pAnd phi psi)
}.

Class OrClosed `{signature} (P : Pattern -> Prop) :=
{
  or_closed : forall phi psi, P phi -> P psi -> P (pOr phi psi)
}.

Class IffClosed `{signature} (P : Pattern -> Prop) :=
{
  iff_closed : forall phi psi, P phi -> P psi -> P (pIff phi psi)
}.

Class FiniteConjunctionClosed `{signature} (P : Pattern -> Prop) :=
{
  finite_conjunction_closed :
    forall phis, Forall P phis -> P (finite_conjunction phis)
}.

Class FiniteDisjunctionClosed `{signature} (P : Pattern -> Prop) :=
{
  finite_disjunction_closed :
    forall phis, Forall P phis -> P (finite_disjunction phis)
}.

Class ExClosed `{signature} (P : Pattern -> Prop) :=
{
  ex_closed : forall x phi, P phi -> P (PEx x phi)
}.

Class AllClosed `{signature} (P : Pattern -> Prop) :=
{
  all_closed : forall x phi, P phi -> P (pAll x phi)
}.

Class MuClosed `{signature} (P : Pattern -> Prop) :=
{
  mu_closed : forall X phi, OccursPositively X phi -> P phi -> P (PMu X phi)
}.

Class NuClosed `{signature} (P : Pattern -> Prop) :=
{
  nu_closed : forall X phi, OccursPositively X phi -> P phi -> P (pNu X phi)
}.

Section sec_pattern_closure_properties.

Context
  `{signature}
  `{!BotClosed P}
  `{!ImplClosed P}.

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

#[export] Instance closed_all `{!ExClosed P} : AllClosed P.
Proof. by constructor; intros x phi Hphi; apply neg_closed, ex_closed, neg_closed. Qed.

End sec_pattern_closure_properties.

Section sec_closed_pattern_closure_properties.

Context `{signature}.

#[export] Instance closed_pattern_bot : BotClosed ClosedPattern.
Proof. by constructor; apply ClosedPattern_elim; cbn; set_solver. Qed.

#[export] Instance closed_pattern_impl : ImplClosed ClosedPattern.
Proof.
  by constructor; intros phi psi [] []; constructor; inversion 1; subst; firstorder.
Qed.

#[export] Instance closed_pattern_ex : ExClosed ClosedPattern.
Proof.
  by constructor; intros x phi []; constructor; inversion 1; subst; firstorder.
Qed.

#[export] Instance closed_pattern_mu : MuClosed ClosedPattern.
Proof.
  by constructor; intros x phi Hpos []; constructor; inversion 1; subst; firstorder.
Qed.

End sec_closed_pattern_closure_properties.
