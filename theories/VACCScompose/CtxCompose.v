
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
Notation tau q := (t • q).
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




(*================ isum =================================*)


Definition isum (p q: proc) := (tau p) + (tau q).

Lemma mp_tau: forall (p e: proc),
  p must_pass e ->  g (tau p) must_pass e.
Proof.
intros p e Hmust.
induction Hmust; eauto with mdb.
eapply m_step; eauto with mdb.
- eexists; do 2 constructor.
- intros p' Htau; inversion Htau; subst; eauto with mdb.
- intros ? ? ? ? ? Htau; inversion Htau.
Qed.


Lemma mp_sum: forall (p q: gproc) (e:proc),
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



Lemma mp_isum: forall (p q e: proc),
  p must_pass e -> q must_pass e -> 
  g (isum p q) must_pass e.
Proof.
intros ? ? ? Hp Hq.
set (lemp:= mp_tau _ _ Hp).
set (lemq:= mp_tau _ _ Hq).
set (lemsum:= mp_sum _ _ _ lemp lemq).
auto.
Qed.



Lemma isuml: forall (p q:proc),  g (isum p q)  ⟶  p.
Proof.
intros; unfold isum. 
constructor; eauto with ccs.
Qed.

Lemma isumr: forall (p q:proc),  g (isum p q)  ⟶  q.
Proof.
intros; unfold isum. 
eapply lts_choiceR; eauto with ccs.
Qed.
 


Lemma mp_isum_rev: forall (p q e: proc),
 g (isum p q) must_pass e -> 
 p must_pass e  /\ q must_pass e.
Proof.
intros ? ? ? Hisum.
dependent induction Hisum; eauto with mdb.
destruct ex as [r trans]; inversion trans; subst; 
try inversion l; subst; split; apply pt; eauto using isuml, isumr.
Qed.


Lemma isum_invert: forall (p q r: proc), g (isum p q)  ⟶  r -> 
  r= p \/ r=q.
Proof.
intros ? ? ? Hisum.
inversion Hisum; subst; inversion H3; subst.
- left; auto.
- right; auto.
Qed.
 
Proposition ctx_compose_isum: forall (p1 p2 q:proc),
  p1 << p2  -> g (isum p1 q) << g (isum p2 q).
Proof.
unfold ctx_pre. 
intros ? ? ? Hmust ? Hfoc.
dependent induction Hfoc; eauto with mdb.
eapply m_step; eauto with mdb.
- eexists; constructor; eauto using isuml.
- intros P Hisum. set (invlem:= isum_invert _ _ _ Hisum).
  destruct invlem; subst; try eapply Hmust; eapply pt;
   eauto using isuml, isumr.
- intros ? ? ? ? ? Hisum; unfold isum in *; inversion Hisum; subst.
  inversion H7; subst. inversion H7.
Qed.





(*================ patched sum =================================*)
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



 
Proposition ctx_compose_patchedsum: forall (p1 p2 q :gproc),
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






(*================== ifthenelse  =============================*)

Lemma mp_iftrue: forall (p q e: proc) E, 
  p must_pass e -> Eval_Eq E = Some true ->
  (If E Then p Else q) must_pass e.
Proof.
intros ? ? ? ? Hmp Hbool.
dependent induction Hmp; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * eexists; do 2 constructor; eauto.
  * eexists; eapply ParRight; eauto.
  * eexists; eapply ParSync; try constructor; eauto.
- intros P Hif.
  inversion Hif; subst; eauto with mdb.
  rewrite Hbool in *; inversion H7. 
- intros P e' ? ? Hpi Hif He.
  inversion Hif; subst; eauto with mdb.
  rewrite Hbool in *; inversion H7.
Qed.

Lemma mp_iffalse: forall (p q e: proc) E, 
  q must_pass e -> Eval_Eq E = Some false ->
  (If E Then p Else q) must_pass e.
Proof.
intros ? ? ? ? Hmp Hbool.
dependent induction Hmp; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * eexists; constructor; eapply lts_ifZero; eauto.
  * eexists; eapply ParRight; eauto.
  * eexists; eapply ParSync; try eapply lts_ifZero; eauto.
- intros P Hif.
  inversion Hif; subst; eauto with mdb.
  rewrite Hbool in *; inversion H7. 
- intros P e' ? ? Hpi Hif He.
  inversion Hif; subst; eauto with mdb.
  rewrite Hbool in *; inversion H7.
Qed.


Lemma mp_iftrue_rev: forall (p q e: proc) E, 
  Eval_Eq E = Some true -> (If E Then p Else q) must_pass e -> 
  p must_pass e.
Proof.
intros ? ? ? ? Hbool Hmp.
dependent induction Hmp; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * inversion l; subst; eexists; constructor; eauto.
    rewrite Hbool in *; inversion H7.
  * eexists; eapply ParRight; eauto.
  * eexists; eapply ParSync; eauto.
    inversion l1; subst; eauto.
    rewrite Hbool in *; inversion H7.
- clear H1 com et H0.
  intros ? Hp.
  eapply pt; constructor; eauto.
- intros ? ? ? ? Hpi Hp He.
  eapply com; try constructor; eauto.
Unshelve. apply (g 𝟘).
Qed. 



(*
Proposition ctx_compose_iffalse: forall (p1 p2 q:proc) E, 
  p1 << p2  -> Eval_Eq E = Some false ->
  (If E Then p1 Else q)  << (If E Then p2 Else q).
Proof.
unfold ctx_pre. 
intros ? ? ? ? Hmust Hbool ? Hfoc.
dependent induction Hfoc; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * inversion l; rewrite Hbool in *; inversion H7; subst.
    eexists; constructor; eapply lts_ifZero; eauto.
  * eexists; eapply ParRight; eauto.
  * inversion l1; subst; rewrite Hbool in *; try inversion H7.
    eexists; eapply ParSync; try eapply lts_ifZero; eauto.
- intros P Hif.
  clear H1 com et H0 H.
  inversion Hif; subst; rewrite Hbool in *; try inversion H4.
Admitted.
*)

(*=================    paralel  =====================================*)

Lemma tau_on_3par: forall p q e:proc, 
 (exists r, (p‖q, e) ⟶ r) -> exists r, (p, q‖e) ⟶ r.
Proof.
intros ? ? ? ex.
destruct ex as [r trans]; inversion trans; subst.
- inversion l; subst; eexists.
  *  eapply ParSync; try constructor; eauto; cbv; auto.
  *  eapply ParSync; try eapply lts_parL; eauto; cbv; auto.
  *  constructor; eauto.
  *  eapply ParRight; eapply lts_parL; eauto.
- eexists; eapply ParRight; eapply lts_parR; eauto.
- inversion l1; subst.
  * eexists; eapply ParSync; eauto; eapply lts_parR; eauto.
  * cbv in eq; destruct μ1,μ2,a0; try (exfalso; apply eq); subst;
    eexists; eapply ParRight; eauto. 
    + eapply lts_comR; eauto.
    + eapply lts_comL; eauto.
Qed.


Lemma mp_frompar: forall (p q r: proc),
  p‖q must_pass r ->  p must_pass q‖r .  
Proof.
intros.
dependent induction H; eauto with mdb.
- apply m_now; constructor; auto.
- set (lem:= good_decidable (q‖ e)); destruct lem.
  * apply m_now; auto.
  * eapply m_step; eauto with mdb.
   + eauto using tau_on_3par.
   + intros; eapply H; try constructor; eauto with ccs.
   + intros E Hqe.
     inversion Hqe; subst.
     ++ eapply H1; eauto. 
        assert (parallel_inter (ActOut (c ⋉ v)) (ActIn (c ⋉ v))). 
        cbv; auto. eauto.        
        eapply lts_parR; eauto.
     ++ eapply H1; eauto. 
        assert (parallel_inter (ActIn (c ⋉ v)) (ActOut (c ⋉ v))). 
        cbv; auto. eauto.        
        eapply lts_parR; eauto.
     ++ eapply H; try eapply lts_parR; eauto.
     ++ eapply H0; eauto.
  + intros ? E ? ? Hpi Hp Hqe.
    inversion Hqe; subst.
    ++ assert (Hpi2:= Hpi).
       destruct μ1,μ2,a0; 
       cbv in Hpi; try (exfalso; apply Hpi); subst.
       +++  eapply H; try eapply lts_comR; eauto.
       +++ eapply H; try eapply lts_comL; eauto.
    ++ eapply H1; try (eapply lts_parL; apply Hp); eauto. 
Qed.


(*
Proposition ctx_compose_par: forall (p1 p2 q:proc), 
  p1 << p2  -> (p1 ‖ q)  << (p2 ‖ q).
Proof.
*)


















 
