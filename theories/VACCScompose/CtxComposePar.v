
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




(* no p =  No One(①) in p    *)
Inductive no: proc -> Prop :=
| no_par: forall p q,   no p -> no q -> no (p‖q)
| no_var: forall x,     no (pr_var x)
| no_rec: forall x p,   no p -> no (pr_rec x p) 
| no_ifthenelse: forall E p q,  
    no p -> no q -> no (If E Then p Else q)
| no_out: forall c v,   no (pr_output c v)
| no_new: forall p,     no p -> no (ν p)
| no_gd:  forall G,     no_g G -> no (g G)
with no_g: gproc -> Prop :=
| nog_nil: no_g 𝟘
| nog_inp: forall c p,    no p -> no_g (gpr_input c p)
| nog_tau: forall p,      no p -> no_g (tau p)
| nog_sum: forall G1 G2,  no_g G1 -> no_g G2 -> no_g (G1+G2)
.
Hint Constructors lts no no_g proc gproc : noh.



(*==========  admitted properties of substitutions  =============*)
Lemma sub_preserve_no: forall p v, no p -> no (sub p v).
Proof.
intros ? ? Hno.
induction Hno; subst; cbn; eauto with noh.
(*constructor; eauto using sub_preserve_nog.*)
admit.
Admitted.


Lemma prsub_preserve_no: forall p q x, no p -> no q -> no (pr_subst x p q).
Proof.
Admitted.


(*========== lemmas on tau-trans ===============================*)

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

Lemma tau_on_3par_rev: forall p q e:proc, 
  (exists r, (p, q‖e) ⟶ r) ->  exists r, (p‖q, e) ⟶ r.
Proof.
intros ? ? ? ex.
destruct ex as [r trans]; inversion trans; subst.
- eexists; do 2 constructor; eauto.
- inversion l; subst.
  * eexists; eapply ParSync; eauto; try eapply lts_parR; 
    try eapply H1; cbv; auto.
  * eexists; eapply ParSync; eauto; try eapply lts_parR; 
    try eapply H2; cbv; auto.
  * eexists; eapply ParLeft; eapply lts_parR; eauto.
  * eexists; eapply ParRight; try eapply lts_parR; eauto.
- inversion l2; subst. 
  * destruct μ1,μ2,a0; cbv in eq; subst; 
    try (exfalso; apply eq); eexists; eapply ParLeft. 
    + eapply lts_comR; eauto.
    + eapply lts_comL; eauto.   
  * eexists; eapply ParSync; try eapply lts_parL; eauto.   
Qed.

(*================= no properties ===================*)
Lemma no_impl_nogood: forall p,  no p -> ~ good_VACCS p.
Proof.
intros. induction H; intro.
inversion H1; subst; destruct H3; auto.
inversion H. inversion H0.
inversion H1; subst; auto.
inversion H. inversion H0; subst; auto.
induction G; try inversion H0; try inversion H; 
subst; firstorder.
Qed.


Lemma lts_preserve_no: forall p q a, lts p a q -> no p -> no q.
Proof. 
intros ? ? ? Hlts.
induction Hlts; intros; try inversion H; try inversion H0;  
subst; auto with noh.
- inversion H1; eauto using sub_preserve_no.
-  inversion H1; auto.
-  eauto using prsub_preserve_no.
- inversion H1; auto with noh.
- inversion H1; auto with noh.
Qed.

(*==============   mp on parallel   =================*)
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
     ++ eapply H1; try eapply lts_parR; eauto; cbv; auto. 
     ++ eapply H1; try eapply lts_parR; eauto; cbv; auto. 
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
 
Lemma mp_topar: forall (p q r: proc), no q ->  
  p must_pass q‖r ->  p‖q must_pass r.  
Proof.
intros ? ? ? Hnoq Hfoc.
dependent induction Hfoc. 
- eapply m_now; inversion H; destruct H1; subst; auto.
  set (lem:= no_impl_nogood _ Hnoq); exfalso; auto.
- eapply m_step.
  * intro; apply nh; eauto with ccs.
  * eauto using tau_on_3par_rev.
  * intros P Hpq; inversion Hpq; subst.
    + eapply H1; try eapply lts_parL; eauto; cbv; auto.
      eauto using lts_preserve_no.
    + eapply H1; try eapply lts_parL; eauto; cbv; auto.
      eauto using lts_preserve_no.
    + eapply H; eauto.
    + eapply H0; try eapply lts_parL; eauto.
      eauto using lts_preserve_no.
  * intros ? Hr; eapply H0; try eapply lts_parR; eauto.
  * intros P r' ? ? Hpi Hpq Hr; inversion Hpq; subst.
    + eapply H1; try eapply lts_parR; eauto.
    + destruct μ1,μ2,a0; cbv in Hpi; try (exfalso; apply Hpi); subst.
       ++ eapply H0; try eapply lts_comR; eauto.
          eauto using lts_preserve_no.
       ++ eapply H0; try eapply lts_comL; eauto.
          eauto using lts_preserve_no.
Qed.
(*===============  composition  ===================*)


Proposition ctx_compose_par: forall (p1 p2 q:proc),  no q -> 
  p1 << p2  -> (p1 ‖ q)  << (p2 ‖ q).
Proof.
repeat intro. Check mp_topar.
apply (mp_topar _ _ _ H (H0 _ (mp_frompar _ _ _ H1))).
Qed.














(*
Lemma sub_preserve_nobla: forall G v k, no (g G) -> 
  no (subst_in_proc k v (g G)) /\ no_g (subst_in_gproc k v G).
Proof. 
intro; induction G; intros; cbn; inversion H; inversion H1; subst; eauto with bla.
- split.
  do 2 constructor. 
  destruct v. simpl. 

Lemma sub_preserve_nog: forall G v, no_g G -> no_g (subst_in_gproc 0 v G).
Proof.
intros ? ? Hnog.
induction Hnog; subst; cbn; eauto with bla.
- admit.
- constructor.
*)
