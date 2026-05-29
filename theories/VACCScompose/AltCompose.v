

(*--------------a bunch of imports--------------------*)
Require Export Must.
Require Export Coq.Program.Equality.
Require Export InputOutputActions ActTau OldTransitionSystems Must  
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.


Require Import DefinitionAS.
Require Import Convergence.
Require Import Termination.
Require Import List.
Require Import stdpp.base.
(*Require Import WeakTransitions.*)



 
(* MVACCS is a local copy of "VACCS_SEQ_Instance" 
   i couldn't import (for idk what reason) "VACCS_SEQ_Instance" 
   so i made a copy of 
   the file "VACCS_SEQ_Instance.v" and named it "MVACCS.v"
   so that after compiling the content become importable.
*)
Require Import MVACCS.  
(*------------------------------------------------------*)


Notation "p ≼ q" := (bhv_pre p q)  (at level 40).
Notation wt := WeakTransitions.wt.







 
 (* HERE:  /!\ what can i do make rocq stop complaining ?   /!\ *) 
 Lemma what_should_i_do : forall p q:proc,
  (p,empty) ≼ (q,empty) -> True.
























(*--------------termination lemmas ---------------*)

Lemma term_tau: forall p:proc, (g(tau p))⤓ -> p⤓.
Proof.
intros; inversion H.
eapply H0; constructor.
Qed.

Lemma term_tau_rev: forall p:proc, p⤓ -> (g(tau p))⤓.
Proof.
intros; constructor; intros. 
inversion H0; subst; auto.
Qed.
(*------------------------------------------------*)   
























(* 
Lemma cnv_compose_tau: forall p q:proc,
  p ≼₁ q -> g (tau p) ≼₁ g (tau q).
Proof.
unfold "≼₁"; intros ? ? Hmust; intros.
destruct s.
- inversion H; subst. 
  eapply term_tau, cnv_nil in H0.
  specialize (Hmust  _ H0); inversion Hmust. 
  constructor; eauto using term_tau_rev.
- constructor; inversion H; subst.
  * eapply term_tau,cnv_nil in H3.
    specialize (Hmust _ H3); inversion Hmust; subst. 
    eauto using term_tau_rev.
  * intros. 
    inversion H0; subst.
    inversion H1; inversion l; subst.
   intros; inversion H1; inversion l; subst.
     
*)






