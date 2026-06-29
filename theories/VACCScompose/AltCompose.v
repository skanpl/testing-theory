
(*--------------a bunch of imports--------------------*)
From Stdlib Require Export Program.Equality.
From TestingTheory Require Export Must VACCS_Good gLts InteractionBetweenLts ActTau.
Include VACCS_Testing.


Require Import DefinitionAS.
Require Import Convergence.
Require Import Termination.
Require Import List.
Require Import stdpp.base.
(*Require Import WeakTransitions.*)
 

Require Import ForwarderConstruction.
(*------------------------------------------------------*)

Print FW_gLts.



Locate MbLts.
Notation wt := WeakTransitions.wt.
Notation tau p := (g (𝛕 • p)).  
Notation inp x p := (g (gpr_input x p)).
Print wt.


Hint Constructors lts :mdb.


Notation Linp c v :=  ( ActTau.ActExt (InputOutputActions.ActIn (c ⋉ v)) ).
Notation Lout c v := ( ActTau.ActExt (InputOutputActions.ActOut (c ⋉ v))  ).
Notation Ltau := ActTau.τ.
Notation sub t1 x1 := (t1 ^ x1).
















(*====================   tau   ==============================*)

(*-------------- convergence lemmas ---------------*)

Lemma term_tau: forall p:proc, (tau p) ⤓ -> p⤓.
Proof.
intros; inversion H.
eapply H0; constructor.
Qed.

Lemma term_tau_rev: forall p:proc, p⤓ -> (tau p)⤓.
Proof.
intros; constructor; intros. 
inversion H0; subst; auto.
Qed.

Lemma cnv_tau: forall p s,
  (tau p)⇓s -> p⇓s.
Proof.
intros.
set (lem:= cnv_preserved_by_lts_tau _ _ H p).
eapply lem; constructor. 
Qed.

Lemma cnv_tau_rev: forall p s,
  p⇓s -> (tau p)⇓s.
Proof.
intros ? ? Hp.
dependent induction Hp; constructor; 
eauto using term_tau_rev.
intros ? Hwt.
inversion Hwt; inversion l; subst.
eapply H0; auto.
Qed.
(*-----------------------------------------*)


(*
Lemma wt_tau: forall q Q s, wt (g (tau q)) s Q -> (~ exists Q', lts Q Ltau Q' ) -> 
  wt q s Q .
Proof.
intros ? ? ? Hwt.
inversion Hwt; subst.
intros.
*)

Lemma lcnv_comp_tau: forall p q,
  p ≼₁ q ->  (tau p)  ≼₁ (tau q) . 
Proof.
unfold "≼₁"; intros ? ? Hplq ? Htaup.
eapply cnv_tau_rev, Hplq, cnv_tau; auto.
Qed.

Lemma lacc_comp_tau: forall p q,
  p ≼₂ q ->  (tau p)  ≼₂ (tau q) . 
Proof.
intros ? ? Hplq. 
unfold "≼₂".
intros s ? Hcnv Hwt Href.
inversion Hwt; try inversion l; subst.
- inversion Href.
- unfold "≼₂" in Hplq.
  eapply cnv_tau in Hcnv.
  specialize (Hplq _ _ Hcnv w Href).
  destruct Hplq as [P [Hwtp [HPref Hsubset]]].
  exists P; repeat split; eauto.
  eapply WeakTransitions.wt_tau; eauto; constructor.
Qed.
  
Proposition alt_comp_tau: forall p q, 
  p ≼ₐₛ q -> tau p ≼ₐₛ tau q.
Proof.
unfold "≼ₐₛ"; intros.
split; try apply lcnv_comp_tau; 
try apply lacc_comp_tau; apply H.
Qed.



(*====================   input   ==============================*)


Lemma wt_inp: forall x q Q mu s,  wt (inp x q) (mu::s) Q -> 
  exists v:Data, ActExt mu = Linp x v /\ wt (sub q v) s Q.
Proof.

intros ? ? ? ? ? Hwt.
inversion Hwt; inversion l; subst.
eexists; split; eauto.
Qed.

Lemma mu_impl_wt: forall p q mu, lts p (ActExt mu) q ->  
  wt p [mu] q.
Proof.
intros ? ? ? Hp.  
eapply WeakTransitions.wt_act; eauto with mdb.
Qed.


Lemma lcnv_comp_inp: forall x p q,
 (forall v, sub p v ≼₁ sub q v) ->  inp x p  ≼₁ inp x q. 
Proof.
unfold "≼₁"; intros ? ? ? Hplq ? Hinp.
destruct s; constructor. 
- constructor; intros ? Hexfal; inversion Hexfal.
- constructor; intros ? Hexfal; inversion Hexfal.
- intros Q Hwt; set (lem:= wt_inp _ _ _ _ _ Hwt).
  destruct lem as [v [Heq Hwtnil]].
  inversion Hinp; inversion Heq; subst.
  specialize (H3 (sub p v)).
  assert (wt (inp x p) [InputOutputActions.ActIn (x ⋉ v)] (sub p v)).
  eapply mu_impl_wt; constructor.
  specialize (Hplq _ _ (H3 H)).
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.




Lemma lacc_comp_inp: forall x p q,
 (forall v, sub p v ≼₂ sub q v) ->  inp x p  ≼₂ inp x q. 
Proof.
intros ? ? ? Hplq.
unfold "≼₂"; intros ? Q Hcnv Hwt Href. 
destruct s. 
- exists (inp x p); repeat split; eauto; try constructor.
  inversion Hwt; try inversion l; subst. 
  (*********) 
   admit.
  (*********)
- set (lem:= wt_inp _ _ _ _ _ Hwt).
  destruct lem as [v [Heq Hwtsub]].
  inversion Heq; subst.
  inversion Hcnv; subst.
  specialize (H3 (sub p v)).
  assert (wt (inp x p) [InputOutputActions.ActIn (x ⋉ v)] (sub p v)).
  eapply mu_impl_wt; constructor.
  specialize (H3 H).
  unfold "≼₂" in Hplq.
  specialize (Hplq _ _ _ H3 Hwtsub Href).
  destruct Hplq as[P[Hwtp [HPref Hsubset]]].
  exists P; repeat split; eauto.
  eapply WeakTransitions.wt_act; try constructor; eauto.
Admitted.


Proposition alt_comp_inp: forall x p q,
  (forall v, sub p v ≼ₐₛ sub q v) -> inp x p ≼ₐₛ inp x q. 
Proof.
unfold "≼ₐₛ"; intros ? ? ? Hplq; split;
try eapply lcnv_comp_inp; try eapply lacc_comp_inp; apply Hplq.
Qed.
