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
  neg_closed : forall ϕ, P ϕ -> P (pNeg ϕ)
}.

Class ImplClosed `{signature} (P : Pattern -> Prop) :=
{
  impl_closed : forall ϕ ψ, P ϕ -> P ψ -> P (PImpl ϕ ψ)
}.

Class AndClosed `{signature} (P : Pattern -> Prop) :=
{
  and_closed : forall ϕ ψ, P ϕ -> P ψ -> P (pAnd ϕ ψ)
}.

Class OrClosed `{signature} (P : Pattern -> Prop) :=
{
  or_closed : forall ϕ ψ, P ϕ -> P ψ -> P (pOr ϕ ψ)
}.

Class IffClosed `{signature} (P : Pattern -> Prop) :=
{
  iff_closed : forall ϕ ψ, P ϕ -> P ψ -> P (pIff ϕ ψ)
}.

Class FiniteConjunctionClosed `{signature} (P : Pattern -> Prop) :=
{
  finite_conjunction_closed :
    forall ϕs, Forall P ϕs -> P (finite_conjunction ϕs)
}.

Class FiniteDisjunctionClosed `{signature} (P : Pattern -> Prop) :=
{
  finite_disjunction_closed :
    forall ϕs, Forall P ϕs -> P (finite_disjunction ϕs)
}.

Class ExClosed `{signature} (P : Pattern -> Prop) :=
{
  ex_closed : forall x ϕ, P ϕ -> P (PEx x ϕ)
}.

Class AllClosed `{signature} (P : Pattern -> Prop) :=
{
  all_closed : forall x ϕ, P ϕ -> P (pAll x ϕ)
}.

Class MuClosed `{signature} (P : Pattern -> Prop) :=
{
  mu_closed : forall X ϕ, OccursPositively X ϕ -> P ϕ -> P (μₚ X ϕ)
}.

Class NuClosed `{signature} (P : Pattern -> Prop) :=
{
  nu_closed : forall X ϕ, OccursPositively X ϕ -> P ϕ -> P (νₚ X ϕ)
}.

Section sec_pattern_closure_properties.

Context
  `{signature}
  `{!BotClosed P}
  `{!ImplClosed P}.

#[export] Instance closed_neg : NegClosed P.
Proof. by constructor; intros ϕ Hϕ; apply impl_closed; [| apply bot_closed]. Qed.

#[export] Instance closed_top : TopClosed P.
Proof. by constructor; apply neg_closed, bot_closed. Qed.

#[export] Instance closed_or : OrClosed P.
Proof. by constructor; intros ϕ ψ Hϕ Hψ; apply impl_closed; [apply neg_closed |]. Qed.

#[export] Instance closed_and : AndClosed P.
Proof.
  by constructor; intros ϕ ψ Hϕ Hψ; apply neg_closed, or_closed; apply neg_closed.
Qed.

#[export] Instance closed_iff : IffClosed P.
Proof. by constructor; intros ϕ ψ Hϕ Hψ; apply and_closed; apply impl_closed. Qed.

#[export] Instance closed_finite_conjunction : FiniteConjunctionClosed P.
Proof.
  by constructor; intros ϕs; induction 1;
    [apply top_closed | apply and_closed].
Qed.

#[export] Instance closed_finite_disjunction : FiniteDisjunctionClosed P.
Proof.
  by constructor; intros ϕs; induction 1;
    [apply bot_closed | apply or_closed].
Qed.

#[export] Instance closed_all `{!ExClosed P} : AllClosed P.
Proof. by constructor; intros x ϕ Hϕ; apply neg_closed, ex_closed, neg_closed. Qed.

End sec_pattern_closure_properties.

Section sec_closed_pattern_closure_properties.

Context `{signature}.

#[export] Instance closed_pattern_bot : BotClosed ClosedPattern.
Proof. by constructor; apply ClosedPattern_elim; cbn; set_solver. Qed.

#[export] Instance closed_pattern_impl : ImplClosed ClosedPattern.
Proof.
  by constructor; intros ϕ ψ [] []; constructor; inversion 1; subst; firstorder.
Qed.

#[export] Instance closed_pattern_ex : ExClosed ClosedPattern.
Proof.
  by constructor; intros x ϕ []; constructor; inversion 1; subst; firstorder.
Qed.

#[export] Instance closed_pattern_mu : MuClosed ClosedPattern.
Proof.
  by constructor; intros x ϕ Hpos []; constructor; inversion 1; subst; firstorder.
Qed.

End sec_closed_pattern_closure_properties.
