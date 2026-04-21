
(*
  /!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\
  /!\                                          /!\
  /!\    a compiler avec les installations:   /!\
  /!\         "coq" et "coq-stdpp"            /!\
  /!\                                         /!\
  /!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\
*)




Require Import Must.
Require Import VACCS_Instance .


From Must Require Import InputOutputActions ActTau OldTransitionSystems Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.

Notation "p << q" := (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p q) (at level 40).
Notation tauact q := (t • q).
Notation sub t1 x1 := (t1 ^ x1).



Require Import Coq.Program.Equality.

(* Tactic that looks for lts/lts_step assumptions and inverts them to
  learn about the shape of the conclusion *)
Ltac lts_inversion :=
try match goal with
| H : lts_step ?p ?a ?q |- _ =>
  solve[inversion H; subst; discriminate || tauto]
| H : lts ?p ?a ?q |- _ => inversion H; subst; discriminate || tauto
 end;
match goal with
| H : lts_step ?p ?a ?q |- _ => inversion H; subst; clear H
| H : lts ?p ?a ?q |- _ => inversion H; subst; clear H
 end.


(*================= tau ==============================*)
Proposition ctx_compose_tau: forall p q, p << q -> 
  (g (gpr_tau p)) << (g (gpr_tau q)).
Proof.
unfold ctx_pre.
Proof.
intros p q Hmust e Hfoc.
dependent induction Hfoc; eauto with mdb.
destruct ex as [r trans].
inversion trans;subst.
- inversion l. subst.
  apply m_step; eauto with mdb.
  * eexists. do 2 constructor.
  * intros p' Hq. lts_inversion. eauto with mdb. 
  * intros. lts_inversion.
- eapply m_step; eauto with mdb.
  * eexists. do 2 constructor.
  * intros p' Hq. lts_inversion.
    clear H1 com H.
    assert (p must_pass e). eapply pt. constructor.
    eapply Hmust. auto. (* Hmust utilisé ici*)
  * intros. lts_inversion.
- lts_inversion. 
Qed.

(*================ input ==========================*)

Proposition ctx_compose_inp: forall c p q,
  (forall v, sub p v << sub q v) ->
  g (gpr_input c p)  << g (gpr_input c q).
Proof.
unfold ctx_pre.
intros c p q Hmust e Hfoc.
dependent induction Hfoc; eauto with mdb.
destruct ex as [r trans].
inversion trans;subst.
- inversion l.
- eapply m_step; eauto with mdb.
  * eexists. eapply ParRight. apply l.
  * intros p' Hq. inversion Hq.
  * intros p' e' μ1 μ2 Hpi Hq He.
    inversion Hq. subst.
    specialize (com (sub p v) e'(ActIn (c ⋉ v)) μ2 Hpi) .
    apply Hmust.
    eapply com; [constructor | auto].
- inversion l1; subst. destruct μ2 as [|c']; inversion eq. subst c'.
  eapply m_step; eauto with mdb.
  * exists (sub q v, b2). eapply ParSync. eauto. constructor. auto.
  * intros. inversion H2.
  * intros q' e' μ1 μ0 Hpi Hq He.
    clear H pt et H0.
    inversion Hq; subst. destruct μ0 as [|c']; inversion Hpi. subst c'.
    clear eq. apply Hmust. eapply com; eauto. constructor.
Qed.


(*
Lemma reinforce_sub: forall v (p q e:proc),
(sub p v) must_pass e  -> 
 (forall e0 : proc, p must_pass e0 -> q must_pass e0) -> 
   (sub q v) must_pass e.
Proof.  
Print subst_in_proc.
*)






