
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




Require Import Coq.Program.Equality.

Proposition bidouille: forall (p q e:proc),
(g (tauact p)) must_pass e  -> 
 (forall e0 : proc, p must_pass e0 -> q must_pass e0) -> 
   (g (tauact q)) must_pass e.
Proof.  
intros p q e Hfoc.
dependent induction Hfoc; eauto with mdb.
destruct ex as [r trans].
inversion trans;subst.
- intro Hmust.
  inversion l. subst.
  eapply m_step; eauto with mdb.
  * eexists. do 2 constructor.
  * intros p' Hq. 
    inversion Hq. subst. eauto with mdb. 
  * intros. inversion H3.
-  intro Hmust.
   eapply m_step; eauto with mdb.
   * eexists. do 2 constructor.
   
   * intros p' Hq.
     inversion Hq. subst. 
     clear H1 com. 
     clear H Hq. (*a priori inutilisable*) 
     assert (p must_pass e). eapply pt. constructor.
     eauto with mdb.
   * intros. inversion H3.
- inversion l1.
Qed.



Proposition ctx_compose_tau: forall p q, p << q -> 
  (g (gpr_tau p)) << (g (gpr_tau q)).
Proof.
intros.
set (lem:= bidouille p q).
unfold "<<".
intros.
unfold "<<" in H.
specialize (lem _ H0 H).
auto.
Qed.









