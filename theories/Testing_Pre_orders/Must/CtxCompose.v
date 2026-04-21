
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



(*================= tau ==============================*)
Lemma reinforce_tau: forall (p q e:proc),
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
     eapply Hmust. auto. (*Hmust utilisé ici*)
   * intros. inversion H3.
- inversion l1.
Qed.


Proposition ctx_compose_tau: forall p q, p << q -> 
  (g (gpr_tau p)) << (g (gpr_tau q)).
Proof.
intros.
set (lem:= reinforce_tau p q).
unfold "<<".
intros.
unfold "<<" in H.
specialize (lem _ H0 H).
auto.
Qed.
(*================ input ==========================*)

Lemma reinforce_inp: forall  c (p q e:proc),
(g (gpr_input c p)) must_pass e  -> 
 (forall e0 : proc, p must_pass e0 -> q must_pass e0) -> 
   (g (gpr_input c q)) must_pass e.
Proof.  
intros c p q e Hfoc.
dependent induction Hfoc; eauto with mdb.
destruct ex as [r trans].
inversion trans;subst.
- inversion l.
- intros Hmust.
  eapply m_step; eauto with mdb.
  * eexists. eapply ParRight. apply l.
  * intros p' Hq. inversion Hq.
  * intros p' e' μ1 μ2 Hpi Hq He. 
    clear H pt.  
    inversion Hq. subst.
   
    specialize (com (sub p v) e'(ActIn (c ⋉ v)) μ2 Hpi) .
    assert (sub p v must_pass e'). eapply com. constructor. auto.
    clear com.
    clear H1. (*a priori impossible a utiliser*)
    
    specialize (et _ l).
    specialize (H0 _ l _ _ eq_refl Hmust).
    (*need a renaming lemma?*)
    admit.   
 
- intro Hmust. 
  inversion l1. subst.
  eapply m_step; eauto with mdb.
  * exists (sub q v, b2). eapply ParSync. eauto. constructor. auto.
  * intros. inversion H2.
  * intros p' e' μ1 μ0 Hpi Hq He.
    clear pt H H0 et. 
    inversion Hq. subst.
    clear H1. (*a priori impossible a utiliser*)   
    (*need a renaming lemma?*)
    admit.    

Admitted.



Proposition ctx_compose_inp: forall c p q,
  p << q -> 
  g (gpr_input c p)  << g (gpr_input c q).
Proof.
intros.
set (lem:= reinforce_inp c p q).
unfold "<<".
intros. 
unfold "<<" in H. 
specialize (lem _ H0 H).
auto.
Qed.




(*
Lemma reinforce_sub: forall v (p q e:proc),
(sub p v) must_pass e  -> 
 (forall e0 : proc, p must_pass e0 -> q must_pass e0) -> 
   (sub q v) must_pass e.
Proof.  
Print subst_in_proc.
*)






