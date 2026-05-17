


Require Import Must.
Require Import VACCS_Instance .


From Must Require Import InputOutputActions ActTau OldTransitionSystems Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.

Notation "p << q" := (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p q) (at level 40).
Notation tau q := (t • q).
Notation sub t1 x1 := (t1 ^ x1).





Lemma inp_nil: forall c v, lts (gpr_input c 𝟘) ((c ⋉ v) ?) (sub  (g 𝟘) v) .
Proof.
intros; cbv; eauto with ccs.
Qed.  




(*============== ~(0 <<c!v) =============*)
Lemma cep1: forall (c : ChannelData),
  (g 𝟘) must_pass g ((tau ①)+ (gpr_input c 𝟘)). 
Proof.
intro.
eapply m_step.
intro.
inversion H; subst.
- destruct H1; inversion H0.
- eexists. eapply ParRight;  eapply lts_choiceL; eauto with ccs.
- intros; inversion H.
- intros; inversion H; subst; inversion H4; subst; 
  apply m_now; eauto with ccs.
- intros; inversion H0.
Qed.



Lemma cep2: forall (c : ChannelData) (v:Data),
  ~ (pr_output c v) must_pass g ((tau ①)+ (gpr_input c 𝟘)). 
Proof.
intros. intro.
inversion H.
- inversion H0; subst; inversion H2; inversion H1.
- specialize (com 𝟘 𝟘). 
  assert (g 𝟘 must_pass g 𝟘).
  eapply com. 
  Focus 2. 
  eapply lts_output.
  Focus 2. 
  eapply lts_choiceR.         
  eapply inp_nil.
  unfold parallel_inter, dual; simpl; eauto.
  inversion H0; try inversion H1.
  destruct ex0 as [r trans]; inversion trans; subst; 
  try inversion l; try inversion l1.
Qed.


Proposition ce: forall (c : ChannelData) (v:Data),
  ~ (g 𝟘) << pr_output c v.
Proof.
intros. intro.
unfold "<<" in H.
specialize (H _ (cep1 c)).
eapply cep2; eauto.
Qed.

(*=================  ~(0 << c?(x).𝟘)  =================================*)  
Lemma ce2p1: forall (c : ChannelData) v,
  (g 𝟘) must_pass pr_output c v‖ g (gpr_input c ①). 
Proof.
intros.
eapply m_step.
- intro; inversion H; subst; destruct H1; inversion H0.
- eexists; eapply ParRight; econstructor; eauto with ccs.
- intros; inversion H.
- intros; inversion H; subst; try inversion H2; try inversion H3; 
  subst; try inversion H4.
  simpl; eapply m_now; constructor; right; constructor.
- intros; inversion H0.
Qed.
    

Lemma ce2p2: forall (c : ChannelData) v,
 ~ g (gpr_input c 𝟘) must_pass pr_output c v‖ g (gpr_input c ①). 
Proof.
intros. intro.
inversion H.
- inversion H0; subst; destruct H2; inversion H1.
- assert ((g 𝟘) must_pass  (g 𝟘)‖ g (gpr_input c ①)). 
  eapply com; try eapply inp_nil; try econstructor; eauto with ccs; cbv; eauto.
  inversion H0.  
  * inversion H1; subst; destruct H3; inversion H2. 
  * destruct ex0 as [r trans]; inversion trans; subst.
    + inversion l.
    + inversion l; subst; try inversion H5. 
      inversion H3. inversion H4. 
    + inversion l1.
Qed.
    
Proposition ce2: forall (c : ChannelData) (v:Data),
  ~  (g 𝟘) << g (gpr_input c 𝟘) .
Proof.
intros. intro.
unfold "<<" in H.
specialize (H _ (ce2p1 c v)).
eapply ce2p2; eauto.
Qed.

(*===============   p+q << p not true in general   ==========================*)


Lemma ce3p1: forall (c : ChannelData) v,
  g (𝟘+ tau (pr_output c v) ) must_pass g (gpr_input c ①). 
Proof.
intros.
apply m_step.
- intro; inversion H.
- eexists; constructor. 
  eapply lts_choiceR; eauto with ccs.
- intros; inversion H; inversion H4; subst; eapply m_step.
  * intro; inversion H0.
  * eexists; eapply ParSync; try econstructor; cbv; eauto.
  * intros; inversion H0.
  * intros; inversion H0.
  * intros. inversion H2; subst; cbn; eapply m_now; constructor. 
- intros; inversion H.
- intros ? ? ? ? Hpi Hsum Hinp. 
  inversion Hsum; subst; inversion H3.
Qed.

Lemma ce3p2: forall (c : ChannelData),
  ~ (g 𝟘) must_pass g (gpr_input c ①). 
Proof.
repeat intro. 
inversion H.
- inversion H0.
- destruct ex as [r trans]; inversion trans; subst; 
  try inversion l; try inversion l1.
Qed.

Lemma ce3: forall c v, 
  ~ g (𝟘+ tau (pr_output c v) ) << g 𝟘 .
Proof.
unfold "<<"; repeat intro.
specialize (H _ (ce3p1 c v)).
eapply ce3p2; eauto.
Qed.




