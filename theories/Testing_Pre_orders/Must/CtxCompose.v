
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



(*=================  attempts ==============================*)

Proposition ctx_compose_new: forall (p q :proc),
  (p << q) -> (exists q0, q ⟶ q0) ->
   (ν p) << (ν q).
Proof.
unfold ctx_pre.
intros p q  Hmust Hqex e Hfoc.
dependent induction Hfoc; eauto with mdb.
destruct ex as [r trans].
inversion trans; subst.

- eapply m_step; eauto with mdb.
  * inversion l. subst. destruct Hqex as [q0 Hqex].
    eexists. do 2 econstructor; eauto. 

  * intros q' Hq.
    clear et H0 com H1. 
    inversion Hq; subst.
    inversion l; subst.
    specialize (pt _ l).
    clear H. (*too strong*)
    (*have to edit "p<<q" like for input...*)
    (*stuck for sure...*)
    admit.
  * intros p' e' μ1 μ2 Hpi Hq He.
    clear et H0.
    inversion Hq; subst.
    clear H H1. (*too strong*)
   admit.
- admit.
- admit.
Admitted.
    





Definition forced (p q: proc) :=
  forall a r, lts q a r -> lts p a r.  

Proposition forced_sum: forall (p1 p2 q r:gproc) a,
  forced p1 p2 -> lts (p2+q) a r -> lts (p1+q) a r .
Proof.
intros ? ? ? ? ? Hforce Hlts.
inversion Hlts; subst.
constructor. eapply Hforce. auto.
eapply lts_choiceR. auto.
Qed.



Proposition mp_sum: forall (p q: gproc) (e:proc),
  (g p) must_pass e -> (g q) must_pass e -> 
  (g (p+q)) must_pass e.
Proof.
intros p q e Hmpp.
dependent induction Hmpp; intros; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst; eexists.
  * do 2 constructor; eauto.
  * eapply ParRight; eauto.
  * eapply ParSync; try constructor; eauto.
- intros P Hpq.
  inversion Hpq; subst.
  * apply pt; auto.
  * inversion H2; eauto with mdb.
- intros E He.
  apply H0; eauto. 
  inversion H2; eauto with mdb.
  exfalso; auto. 
- intros P E ? ? Hpi Hpq He.
  inversion Hpq; subst.
  * eapply com; eauto with mdb.
  * inversion H2; eauto with mdb.
    exfalso; auto. 
Qed.

 
Proposition ctx_compose_sum: forall (p1 p2 q :gproc),
  g p1 << g p2 -> (exists p0, g p2 ⟶ p0) ->  forced p1 p2  -> 
  g (p1 + q) << g (p2 + q).
Proof.
unfold ctx_pre. 
intros p1 p2 q Hmust Hex Hforce e Hfoc.

dependent induction Hfoc; eauto with mdb.
destruct ex as [r trans]; inversion trans;subst.
- eapply m_step; eauto with mdb.
  * destruct Hex; eexists; do 2 constructor; eauto.
  * intros ? Hp2q.
    eapply pt.
    inversion Hp2q; subst.
    + constructor; eapply Hforce; auto.
    + eapply lts_choiceR; auto.
  * intros ? ? ? ? Hpi Hp2q He.
    eapply com; eauto with mdb.
    inversion Hp2q; subst.
    + constructor; eapply Hforce; auto.
    + eapply lts_choiceR; auto.
- eapply m_step; eauto with mdb.
  * eexists; eapply ParRight; eauto.
  * intros P Hp2q.
    clear H.
    clear com H1.
    
    clear et H0.
  
    inversion Hp2q; subst;eapply pt.
    + constructor; eapply Hforce; auto.
    + eapply lts_choiceR; auto.
  *  intros ? ? ? ? Hpi Hp2q He.
     clear H H1.
     
     inversion Hp2q; subst.
     + eapply com. eapply Hpi.
       constructor. eapply Hforce. auto. auto.      
     + eapply com. eapply Hpi.
       eapply lts_choiceR. auto. auto.

- eapply m_step; eauto with mdb.    
  * destruct Hex as [p0 p2step].
    eexists. do 2 constructor.
    eauto.
  * intros ? Hp2q. 
    eapply pt. 
    inversion Hp2q; subst.
    + constructor; eapply Hforce; auto.
    + eapply lts_choiceR; auto.
  * intros ? ? ? ? Hpi Hp2q He.
    eapply com; eauto.
     inversion Hp2q; subst.
     + constructor. eapply Hforce. auto.       
     + eapply lts_choiceR. auto.
Qed.







(*
observation: in all the things we've done so far one of the "generated IH" each time called "H" requires a way too strong precond to be used which makes it unusable.
*)
 



