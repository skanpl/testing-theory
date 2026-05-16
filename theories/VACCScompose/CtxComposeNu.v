
(*---------- very temporary don't pay attention to this -------------------*)
Require Import Must.
Require Import VACCS_Instance .
From Must Require Import InputOutputActions ActTau OldTransitionSystems Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.
Notation "p << q" := (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p q) (at level 40).
Notation tau q := (t • q).
Notation sub t1 x1 := (t1 ^ x1).
Require Import Coq.Program.Equality.
(*-----------------------------------------------------------------------*)










(*============== admitted properties ================*)

Fixpoint shift (p:proc) : proc. Admitted.
Notation ash mu :=  (VarC_action_add 1 mu).

(*--------shift on lts -----------------*)
Lemma lts_shift_mu: forall (p q:proc) (mu:ExtAct TypeOfActions),
  lts p (ActExt mu) q -> lts (shift p) (ActExt ( ash mu)) (shift q).


Proof. 
Admitted.

Lemma lts_shift_tau: forall (p q:proc),
  lts p τ q -> lts (shift p) τ (shift q).


Proof. 
Admitted.

Lemma lts_shift_inv_tau: forall (p q:proc), lts (shift p) τ q -> 
  exists p', lts p τ p' /\ q = shift p'.

Proof. 
Admitted.

 
Lemma lts_shift_inv_mu: forall (p q:proc) (mu:ExtAct TypeOfActions), 
  lts (shift p) (ActExt mu) q -> 
  exists p' mu0, lts p (ActExt mu0) p' /\ q = shift p' /\ mu= ash mu0.

Proof. 
Admitted.

(*---------- shift  on dual predicate  --------------------*)
Lemma dual_shift: forall (mu1 mu2:ExtAct TypeOfActions),
  parallel_inter mu1 mu2 ->
  parallel_inter (ash mu1) (ash mu2).

Proof. 
Admitted.



Lemma dual_shift_inv: forall mu1 mu2, parallel_inter mu1 (ash mu2) ->
  exists mu0, mu1 = ash mu0 /\ parallel_inter mu0 mu2.

Proof. 
Admitted.
(*------------- other stuff --------------------------*)
	
Lemma ash_inj: forall (mu1 mu2:ExtAct TypeOfActions), 
  ash mu1 = ash mu2 -> mu1=mu2.

Proof. 
Admitted.



Lemma good_shift: forall (e:proc), 
  good_VACCS e <-> good_VACCS (shift e).

Proof. 
(*NB to prove this you need to generalize from shift to an 
  arbitrary substitution sigma because of lifting.
*) 
Admitted.




(*=========== new compose tentatives   ====================*)
 
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
  


 
(*=============================================*)
 


Lemma mp_tonu: forall (p e: proc),
  p must_pass shift e -> ν p must_pass e.
Proof.
intros.
dependent induction H; eauto with mdb.
- eapply m_now; destruct (good_shift e); firstorder.
- eapply m_step.
  * destruct (good_shift e); clear pt H et H0 com H1 ex; firstorder.
  * destruct ex as [r trans]; inversion trans; subst.
    + eexists; do 2 constructor; eauto.
    + set (lem:= lts_shift_inv_tau _ _ l); destruct lem as [e0 [G1 G2]]; 
      eexists; eapply ParRight; eauto.
    + set (leme:= lts_shift_inv_mu _ _ _ l2).
      destruct leme as [e' [mu0 [He [b2eq mu2eq]]]]; subst.
      set (lem:= dual_shift_inv _ _ eq).
      destruct lem as [mu1 [mu1eq Hpi12]]; subst.
      eexists; eapply ParSync; eauto.
      constructor; eauto.
  * intros P Hnup.    (*observe the hypo H *)
    inversion Hnup; subst; eauto.
  * intros e' He. (*observe the hypo H0 *)
    admit.
  * intros P e' ? ? Hpi Hnup He.
    set (lem:= dual_shift _ _ Hpi). 
    inversion Hnup; subst.
    eapply H1; try apply lem; try eapply lts_shift_mu ; eauto.
Admitted.



 

 


Lemma mp_fromnu: forall (p e: proc),
  ν p must_pass e -> p must_pass shift e.
Proof.
intros.
dependent induction H; eauto with mdb.
- eapply m_now; destruct (good_shift e); firstorder.
- eapply m_step.
  * destruct (good_shift e); clear pt H et H0 com H1 ex; firstorder.
  * destruct ex as [r trans]; inversion trans; subst.
    + inversion l; subst; eexists; constructor; eauto.
    + eexists; eapply ParRight; set (lem:= lts_shift_tau _ _ l); eauto.
    + inversion l1; subst. set (lem:= lts_shift_mu _ _ _ l2);
      eexists; eapply ParSync; try eapply dual_shift; eauto.
  * intros p' Hp.
    admit.
  * intros e' Hse.
    set (lem:= lts_shift_inv_tau _ _ Hse).
    destruct lem as [e1 [He Heeq]]; subst; eauto.
  * intros p' E ? ? Hpi Hp Hse.
    cbv in Hpi. 
    admit.
Admitted.   


Proposition  ctx_compose_nu: forall (p q: proc),
  p << q -> (ν shift p) << (ν shift q). 
Proof.
unfold "<<"; intros ? ? Hmust ? Hfoc.
dependent induction Hfoc; eauto with mdb.
eapply m_step; eauto with mdb.
- admit. 
- intros Q Hnsq.
  inversion Hnsq; subst. 
  set (lem:= lts_shift_inv_tau _ _ H3).
  destruct lem as [q' [Hq Hsheq]]; subst.
  admit.
- intros Q e' ? ? Hpi Hsq He.
  admit.
Admitted.










(*  bidouillage

Print good_VACCS.
Print lts.

Definition lift (sigma:proc-> proc) (p:proc) :proc. Admitted.

Lemma sbsimpl: forall (p:proc) (sigma:proc ->proc),
  sigma (ν p) =  ν ((lift sigma) p) .
Proof. Admitted.

*)

