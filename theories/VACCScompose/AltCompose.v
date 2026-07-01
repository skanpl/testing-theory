
(*--------------a bunch of imports--------------------*)
From Stdlib Require Export Program.Equality .
From TestingTheory Require Export Must VACCS_Good gLts InteractionBetweenLts ActTau.
Include VACCS_Testing.


Require Import DefinitionAS.
Require Import Convergence.
Require Import Termination.
Require Import List.
Require Import stdpp.base.
(*Require Import WeakTransitions.*)
 

Require Import ForwarderConstruction.


(*-----temporary ???-----*)
From stdpp Require Import gmap.
(*--------------------*)
(**)
(*------------------------------------------------------*)

Print FW_gLts.



Locate MbLts.
Notation wt := WeakTransitions.wt.
Notation tau p := (g (𝛕 • p)).  
Notation inp x p := (g (gpr_input x p)).
Print wt.


Hint Constructors lts :mdb.


Notation Linp c v :=  ( ActTau.ActExt (InputOutputActions.ActIn (c ⋉ v)) ).
Notation Lout c v := ( ActTau.ActExt (InputOutputActions.ActOut (c ⋉ v))  ).
Notation Ltau := ActTau.τ.
Notation sub t1 x1 :=  (subst_in_proc 0 x1 t1).

Locate "^".














(*====================   tau   ==============================*)

(*-------------- convergence lemmas ---------------*)

Lemma term_tau: forall p:proc, (tau p) ⤓ -> p⤓.
Proof.
intros ? H; inversion H.
eapply H0; constructor.
Qed.

Lemma term_tau_rev: forall p:proc, p⤓ -> (tau p)⤓.
Proof.
intros; constructor; intros ? Htau. 
inversion Htau; subst; auto.
Qed.

Lemma cnv_tau: forall p s,
  (tau p)⇓s -> p⇓s.
Proof.
intros.
set (lem:= cnv_preserved_by_lts_tau _ _ H p).
eapply lem; constructor. 
Qed.

Lemma cnv_tau_rev: forall p s,
  p⇓s -> (tau p)⇓s.
Proof.
intros ? ? Hp.
dependent induction Hp; constructor; 
eauto using term_tau_rev.
intros ? Hwt.
inversion Hwt; inversion l; subst.
eapply H0; auto.
Qed.
(*-----------------------------------------*)
 

Lemma lcnv_comp_tau: forall p q,
  p ≼₁ q ->  (tau p)  ≼₁ (tau q) . 
Proof.
unfold "≼₁"; intros ? ? Hplq ? Htaup.
eapply cnv_tau_rev, Hplq, cnv_tau; auto.
Qed.

Lemma lacc_comp_tau: forall p q,
  p ≼₂ q ->  (tau p)  ≼₂ (tau q) . 
Proof.
intros ? ? Hplq. 
unfold "≼₂".
intros s ? Hcnv Hwt Href.
inversion Hwt; try inversion l; subst.
- inversion Href.
- unfold "≼₂" in Hplq.
  eapply cnv_tau in Hcnv.
  specialize (Hplq _ _ Hcnv w Href).
  destruct Hplq as [P [Hwtp [HPref Hsubset]]].
  exists P; repeat split; eauto.
  eapply WeakTransitions.wt_tau; eauto; constructor.
Qed.
  
Proposition alt_comp_tau: forall p q, 
  p ≼ₐₛ q -> tau p ≼ₐₛ tau q.
Proof.
unfold "≼ₐₛ"; intros.
split; try apply lcnv_comp_tau; 
try apply lacc_comp_tau; apply H.
Qed.



(*====================   input   ==============================*)


Lemma wt_inp: forall x q Q mu s,  wt (inp x q) (mu::s) Q -> 
  exists v:Data, ActExt mu = Linp x v /\ wt (sub q v) s Q.
Proof.

intros ? ? ? ? ? Hwt.
inversion Hwt; inversion l; subst.
eexists; split; eauto.
Qed.

Lemma mu_impl_wt: forall p q mu, lts p (ActExt mu) q ->  
  wt p [mu] q.
Proof.
intros ? ? ? Hp.  
eapply WeakTransitions.wt_act; eauto with mdb.
Qed.


Lemma lcnv_comp_inp: forall x p q,
 (forall v, sub p v ≼₁ sub q v) ->  inp x p  ≼₁ inp x q. 
Proof.
unfold "≼₁"; intros ? ? ? Hplq ? Hinp.
destruct s; constructor. 
- constructor; intros ? Hexfal; inversion Hexfal.
- constructor; intros ? Hexfal; inversion Hexfal.
- intros Q Hwt; set (lem:= wt_inp _ _ _ _ _ Hwt).
  destruct lem as [v [Heq Hwtnil]].
  inversion Hinp; inversion Heq; subst.
  specialize (H3 (sub p v)).
  assert (wt (inp x p) [InputOutputActions.ActIn (x ⋉ v)] (sub p v)).
  eapply mu_impl_wt; constructor.
  specialize (Hplq _ _ (H3 H)).
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.



Lemma lacc_comp_inp: forall x p q,
 (forall v, sub p v ≼₂ sub q v) ->  inp x p  ≼₂ inp x q. 
Proof.
intros ? ? ? Hplq.
unfold "≼₂"; intros ? Q Hcnv Hwt Href. 
destruct s. 
- exists (inp x p); repeat split; eauto; try constructor.
  inversion Hwt; try inversion l; subst. 
  
  (**** tentativede preuve 
         R(x?(y).p)⊆R(x?(y).q )*****)
   clear  Hwt Href Hcnv Hplq.
   intro. intro. 
   destruct H as [mu [G1 G2]]; subst. 
   exists mu.  
   split. 
   + destruct G1 as [mu0 [G1 [G2 G3]]].
     exists mu0; repeat split; eauto.
     intro. inversion H.  
     destruct mu0, (decide (ChannelData_of a = x)).
     * inversion H1.
     * admit.
     * admit.
     * admit.
   + unfold 𝝳ᴠᴀᴄᴄꜱ, "∘", Φᴠᴀᴄᴄꜱ.
     destruct mu,a; auto.      
  (*********)
- set (lem:= wt_inp _ _ _ _ _ Hwt).
  destruct lem as [v [Heq Hwtsub]].
  inversion Heq; subst.
  inversion Hcnv; subst.
  specialize (H3 (sub p v)).
  assert (wt (inp x p) [InputOutputActions.ActIn (x ⋉ v)] (sub p v)).
  eapply mu_impl_wt; constructor.
  specialize (H3 H).
  unfold "≼₂" in Hplq.
  specialize (Hplq _ _ _ H3 Hwtsub Href).
  destruct Hplq as[P[Hwtp [HPref Hsubset]]].
  exists P; repeat split; eauto.
  eapply WeakTransitions.wt_act; try constructor; eauto.
Admitted.


Proposition alt_comp_inp: forall x p q,
  (forall v, sub p v ≼ₐₛ sub q v) -> inp x p ≼ₐₛ inp x q. 
Proof.
unfold "≼ₐₛ"; intros ? ? ? Hplq; split;
try eapply lcnv_comp_inp; try eapply lacc_comp_inp; apply Hplq.
Qed.


(*==================  Nu  =============================*)

Notation ash mu :=  (VarC_action_add 1 mu).

(*shift on trace*)
Fixpoint sh s := match s with
  | nil   => nil
  | mu::s' => (ash mu):: sh s'  
end.



Lemma shift_nil: forall s, nil=sh s -> s=nil.
Proof. 
intros ? H; destruct s; auto.
cbn in H; inversion H.
Qed.

Lemma shift_cons: forall mu s s', mu::s'=sh s -> 
  exists mu0 s0, s=mu0::s0 /\ 
  mu= ash mu0 /\ s'=sh s0.
Proof.
intros ? ? ? H; destruct s; cbn in *; 
inversion H; eauto.
Qed.


Lemma wt_unshift: forall p q s, wt p (sh s) q -> 
  wt (ν p) s (ν q).  
Proof.
intros ? ? ? Hwt.
dependent induction Hwt.
- apply shift_nil in x; subst; constructor.
- specialize (IHHwt s JMeq_refl);  
  eapply WeakTransitions.wt_tau;  
  try constructor; eauto. 
- apply shift_cons in x.
  destruct x as [mu0[s1[Heqs[Heqmu Heqs0]]]]; subst.
  specialize (IHHwt _ JMeq_refl).  
  eapply WeakTransitions.wt_act; 
  try constructor; eauto.
Qed.


Lemma wt_unshiftmu: forall p q mu, wt p [ash mu] q -> 
  wt (ν p) [mu] (ν q).  
Proof.
eauto using wt_unshift.
Qed.


Lemma wt_shift: forall p Q s, wt (ν p) s Q -> 
  exists p', wt p (sh s)  p' /\ Q=ν p'.
Proof.
intros ? ? ? Hwt.
dependent induction Hwt; eauto with mdb. 
- inversion l; subst. 
  specialize (IHHwt _ eq_refl). 
  destruct IHHwt as [p''[Hwtp' Heq]]. 
  eauto with mdb.
- inversion l; subst.
  specialize (IHHwt _ eq_refl).
  destruct IHHwt as [p''[Hwtp' Heq]]; subst. 
  exists p''; split; 
  try eapply WeakTransitions.wt_act; eauto.
Qed.

Lemma wt_shiftmu: forall p Q mu, wt (ν p) [mu] Q -> 
  exists p', wt p [ash mu]  p' /\ Q=ν p'.
Proof. 
intros ? ? ? H.
eauto using (wt_shift _ _ _ H).
Qed.



Lemma term_nu: forall p, (ν p)⤓ -> p⤓.
Proof.
intros ? Hter; dependent induction Hter. 
constructor; intros p' Hp.
eapply H0; constructor; eauto.
Qed.

Lemma term_nu_rev: forall p, p⤓ -> (ν p)⤓.
Proof.
intros ? Hter; dependent induction Hter.
constructor; intros P Hnup; inversion Hnup.
eauto with mdb.
Qed.






Lemma cnv_nu: forall s p,
  (ν p)⇓s -> p⇓(sh s) .
Proof.
intros ? ?; generalize dependent p. 
induction s; intros ? Hcnv; 
inversion Hcnv; subst; cbn in *; 
try (constructor; auto using term_nu). 
intros p' Hwt; inversion Hwt; subst.
- eapply wt_unshiftmu in w.
  eapply IHs, H3, wt_unshiftmu; auto.
- apply lts_res_ext, mu_impl_wt in l.
  specialize (H3 _ l); specialize (IHs _ H3).
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.

Lemma cnv_nu_rev: forall s p,
  p⇓(sh s) -> (ν p)⇓s.
Proof.
intros ? ? Hcnv.
dependent induction Hcnv.
- apply shift_nil in x; subst; constructor;
  auto using term_nu_rev.
- apply shift_cons in x; subst.
  destruct x as [mu0 [s1 [Heqs [Heqmu Heqs0]]]]; subst.
  constructor; auto using term_nu_rev.
  intros P Hwt; apply wt_shiftmu in Hwt.
  destruct Hwt as [p' [Hwt Heq]]; subst; eauto.
Qed.


Lemma lcnv_comp_nu: forall p q,
  p ≼₁ q ->  (ν p)  ≼₁ (ν q) . 
Proof.
unfold "≼₁"; intros ? ? Hplq ? Htaup.
eapply cnv_nu_rev, Hplq, cnv_nu; auto.
Qed.



Lemma lacc_comp_nu: forall p q,
  p ≼₂ q ->  (ν p)  ≼₂ (ν q) . 
Proof.
intros ? ? Hplq; unfold "≼₂".
intros ? Q Hcnv Hwt Href.
apply wt_shift in Hwt.
apply cnv_nu in Hcnv.
unfold "≼₂" in Hplq.
destruct Hwt as [q'[Hwt Heq]]; subst.
specialize (Hplq _ _ Hcnv Hwt).
assert (q' ↛). set_solver.
specialize (Hplq H).
destruct Hplq as [p0 [Hwtp [Hrefp0 Hsubset]]]; subst.
exists (ν p0); repeat split.
- apply wt_unshift, Hwtp.
- set_solver.
- intro. intro. 
  destruct H0 as [mu [G1 G2]].
  assert (mu ∈ Subset_Act.coR p0).
  unfold Subset_Act.coR in *.
  destruct G1 as [mu0 [K1 [K2 K3]]]. 
  eexists; repeat split; eauto. 
  intro. apply K1. 
  admit.
  econstructor; split; eauto.
  admit.
Admitted.
