
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



(*================= new   ==============================*)
 
Fixpoint shift (p:proc) : proc. Admitted.


Notation ash mu :=  (VarC_action_add 1 mu).


Lemma lts_shift_mu: forall (p q:proc) (mu:ExtAct TypeOfActions),
  lts p (ActExt mu) q -> lts (shift p) (ActExt ( ash mu)) (shift q).
Proof. Admitted.

Lemma lts_shift_tau: forall (p q:proc),
  lts p τ q -> lts (shift p) τ (shift q).
Proof. Admitted.

Lemma lts_shift_inv_tau: forall (p q:proc), lts (shift p) τ q -> 
  exists p', lts p τ p' /\ q = shift p'.
Proof. Admitted.
 
Lemma lts_shift_inv_mu: forall (p q:proc) (mu:ExtAct TypeOfActions), 
  lts (shift p) (ActExt mu) q -> 
  exists p' mu0, lts p (ActExt mu0) p' /\ q = shift p' /\ mu= ash mu0.
Proof. Admitted.

Lemma dual_shift: forall (mu1 mu2:ExtAct TypeOfActions),
  parallel_inter mu1 mu2 ->
  parallel_inter (ash mu1) (ash mu2).
Proof. Admitted.
	
Lemma ash_inj: forall (mu1 mu2:ExtAct TypeOfActions), 
  ash mu1 = ash mu2 -> mu1=mu2.
Proof. Admitted.

Proposition mp_new: forall (p e :proc),
   p must_pass e -> ν (shift p) must_pass e.
Proof.
intros.
dependent induction H; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * eexists; do 2 constructor.
    set (lem:= lts_shift_tau _ _ l); eauto.
  * eexists. eapply ParRight. apply l.
  * eexists. 
    eapply ParSync; eauto.
    constructor.
    set (lem:= lts_shift_mu _ _ _ l1). eauto.
- intros P Hsp.
  inversion Hsp; subst. 
  set (lem:= lts_shift_inv_tau _ _ H3).
  destruct lem as [p1 [Hp Hs]]; subst.
  eapply H; auto.
- intros P ? ? ? Hpi Hsp He.
  inversion Hsp; subst.  
  set (lem:= lts_shift_inv_mu _ _ _ H4).
  destruct lem as [p1 [mu [Hp [Hspeq Hsmu]]]]; subst.
  eapply H1. 
  Focus 2. eauto.
  set (leminj:= ash_inj _ _ Hsmu). 
  symmetry in leminj. rewrite leminj.
  eauto. eauto.
Qed. 
  

(*
Proposition mp_new_rev: forall (p e :proc),
  ν (shift p) must_pass e ->  p must_pass e.
Proof.
intros.
dependent induction H. eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * inversion l; subst.
    set (lem:= lts_shift_inv_tau _ _ H3).
    destruct lem as [p1 [Hp Hs]]; subst.
    eexists. constructor. eauto.
  * eexists. apply ParRight; apply l.
  * inversion l1; subst. 
    set (lem:= lts_shift_inv_mu _ _ _ H4).
    destruct lem as [p1 [mu [Hp [Hspeq Hsmu]]]]; subst.
    
    eexists. eapply ParSync.
    Focus 2. eauto. 
    set (leminj:= ash_inj _ _ Hsmu). 
    symmetry in leminj. rewrite leminj.
    eauto. eauto.
- intros ? Hp.
  specialize (pt (ν shift p')). 
  admit.
- intros.
Admitted.
*)  


Lemma good_shift: forall (e:proc), 
  good_VACCS e -> good_VACCS (shift e).
Proof. Admitted.
Lemma notgood_shift: forall (e:proc), 
  (~ good_VACCS e) -> ~ good_VACCS (shift e).
Proof. Admitted.

Lemma dual_shift_inv: forall mu1 mu2, parallel_inter mu1 (ash mu2) ->
  exists mu0, mu1 = ash mu0 /\ parallel_inter mu0 mu2.
Proof. Admitted.



Proposition mp_new_bis: forall (p e :proc),
   ν p must_pass e -> p must_pass shift e .
Proof.
intros.
dependent induction H.
- eapply m_now; eapply good_shift; eauto.
- eapply m_step.
  * apply notgood_shift; auto.
  * destruct ex as [r trans]; inversion trans; subst.
    + inversion l; subst; eexists; constructor; eauto.
    + eexists; apply ParRight; eapply lts_shift_tau; eauto.
    + inversion l1; subst.
      set (lem:= lts_shift_mu _ _ _ l2).
      set (lemdual:= dual_shift _ _ eq).
      eexists; eapply ParSync; try eapply lemdual; eauto. 
  * intros ? Hp. admit.
  * intros ? Hse.
    set (lem:= lts_shift_inv_tau _ _ Hse).
    destruct lem as [e1 [He Hseq]]; subst.
    eapply H0; eauto.
  * intros ? ? ? ? Hpi Hp Hse.
    set (lem:= lts_shift_inv_mu _ _ _ Hse).
    destruct lem as [e1 [mu0 [He [Hseq Hmueq]]]]; subst.
    set (lem:= dual_shift_inv _ _ Hpi).
    destruct lem as [mu1 [Hsmu1 Hpi2]]; subst.       
 eapply com. apply Hpi2. 
Admitted.


Proposition mp_new_rev: forall (p e :proc),
  ν p must_pass e ->  shift p must_pass e.
Proof.
intros.
dependent induction H. eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * inversion l; subst.
    set (lem:= lts_shift_tau _ _ H3).
    eexists; constructor; eauto.
  * eexists; apply ParRight; apply l.
  * inversion l1; subst.
    set (lem:= lts_shift_mu _ _ _ H4).
    eexists. eapply ParSync.
    Focus 2. eauto.
Admitted.    
  

(*
Proposition ctx_compose_new: forall (p q :proc),
  ( p << q)  ->
   (ν p) << (ν q).
Proof.
unfold ctx_pre.
intros p q  Hmust e Hmustnu.
inversion Hmustnu; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * inversion l; subst.
    specialize (pt _ l).
    

    set (lem:= mp_new_rev _ _ Hmustnu).
    set (lem2:= mp_shift _ _ lem).
    specialize (Hmust _ lem2).
    admit.
   * eexists. apply ParRight; eauto.
   * admit.
- intros Q Hq.
  inversion Hq; subst.
  inversion Hmustnu; eauto with mdb.
*)  


(*=================================================*)


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
 



