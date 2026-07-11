


Require Import AltGenerality.

















Notation ash mu :=  (VarC_action_add 1 mu). (*ash=action shift*)
Notation alpha := (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ). (*abstraction on a mu*)
Notation Alpha := (Subset_Act.map_set alpha). (*abstraction on a set of mus*)


(*shift on trace*)
Fixpoint sh s := match s with
  | nil   => nil
  | mu::s' => (ash mu):: sh s'  
end.







(*================ admitted stuff ================================*)
Lemma dual_shift: forall mu1 mu2,
  dual mu1 mu2 ->
  dual (ash mu1) (ash mu2).
Proof. Admitted.

Lemma blocking_shift: forall mu,
  blocking mu -> blocking (ash mu).
Proof. Admitted. 

Lemma blocking_shift_rev: forall mu,
  blocking (ash mu) -> blocking mu.
Proof. Admitted. 


Lemma shift_procstable_inv: forall p mu, 
  proc_stable p (ActExt (ash mu)) ->
  proc_stable p (ActExt mu) .
Proof. Admitted. 


Lemma dual_shift_inv: forall mu1 mu2, dual mu1 (ash mu2) ->
  exists mu0, mu1 = ash mu0 /\ dual mu0 mu2.
Proof. Admitted.

Lemma inv_alpha: forall mu1 mu2,
  alpha (ash mu1) = alpha mu2 -> 
  exists mu0, mu2 = ash mu0 /\ alpha mu1 = alpha mu0 .
Proof. Admitted. 
 
(*=========================================================*)


(*-----------misc----------------------*)
Lemma inv_nonmublock_precise: forall p mu,
  (¬ (p ↛[mu])) -> exists x v q,
  
  ((ActExt mu) =  Linp x v /\ lts p (Linp x v) q)  \/ 
  ((ActExt mu) =  Lout x v /\lts p (Lout x v) q) .
Proof.
intros ? ? Hnmb.
simpl in Hnmb.
unfold proc_stable, lts_set in *.
destruct (inv_mu mu) as [x [v H]].
destruct H as [H|H]; inversion H; subst; eauto.
- set (empdec:=  set_choose_or_empty (lts_set_input p (x ⋉ v))) .
  destruct empdec as [empdec|empdec].
  * destruct empdec as [q empdec]. set (lem:= lts_set_input_spec0 _ _ _ empdec).
     repeat eexists; eauto.
  * set_solver.
- set (empdec:=  set_choose_or_empty (lts_set_output p (x ⋉ v))) .
  destruct empdec as [empdec|empdec].
  * destruct empdec as [q empdec]. set (lem:= lts_set_output_spec0 _ _ _ empdec).
     repeat eexists; eauto.
  * set_solver.
Qed.


Lemma inv_nonmublock: forall p mu,
  (¬ (p ↛[mu])) -> exists q, lts p (ActExt mu) q  .
Proof.
intros ? ? H. set (lem:= inv_nonmublock_precise _ _ H).
destruct lem as [x [c [q [[Heq lem]|[Heq lem]]]]]; rewrite Heq; eauto.
Qed.


Lemma inv_nonmublock_rev: forall p mu,
  (exists q, lts p (ActExt mu) q)  -> (¬ (p ↛[mu]))  .
Proof.
intros ? ? H. 
destruct H as [q Hlt].
intro.
set (lem := inv_mu mu).
destruct lem as [x [v [Hmueq|Hmueq]]]; inversion Hmueq; subst.
- eapply lts_set_input_spec1 in Hlt; set_solver.
- eapply lts_set_output_spec1 in Hlt; set_solver.
Qed.

Lemma nonref_nu: forall p mu, 
  ¬ (ν p) ↛[mu]  ->  ¬ p ↛[ash mu] .
Proof.
intros ? ? H. 
set (lem:= inv_nonmublock _ _ H).
destruct lem as [q Hlt].
inversion Hlt; subst.
eauto using inv_nonmublock_rev.
Qed.

Lemma nonref_nu_rev: forall p mu, 
  ¬ p ↛[ash mu] -> ¬ (ν p) ↛[mu].
Proof.
intros ? ? H. 
set (lem:= inv_nonmublock _ _ H).
destruct lem as [q Hlt]. 
apply lts_res_ext in Hlt.
eauto using inv_nonmublock_rev.
Qed.



(*----------------trace------------------------*)
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
(*----------weak transitions ------------------*)

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
(*------------ convergence -----------------*)


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

(*-------------- composition --------------*)

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

(*=============== ready set inclusion =================*)
- intro. intro.
  destruct H0 as [mu [G1 G2]].
  destruct G1 as [mu0 [F1 [F2 F3]]].
  
    (*---------assertion1---------------*) 
    assert( (alpha (ash mu))∈ Alpha (Subset_Act.coR p0)).  
   eexists; split; eauto.
     apply dual_shift in F2; apply blocking_shift in F3.
     exists (ash mu0); repeat split; auto.
     auto using nonref_nu.
   (*----------assertion2-----------------------*)
    assert (alpha (ash mu)
    ∈ Alpha (Subset_Act.coR q')).
    set_solver.
   (*---------------------------------*)
    clear Hwtp Hrefp0 Hcnv Hwt Href H. 
    clear H0.
    destruct H1 as [mu1 [T D]]; destruct T as [mu2 [T1 [T2 T3]]].
    apply inv_alpha in D; destruct D as [mu3 [Heq1 Heqalph]]; subst.
    apply dual_shift_inv in T2; destruct T2 as [mu4 [S1 S2]]; subst.
    eexists; split; eauto.  
    eexists; repeat split; eauto using nonref_nu_rev. 
    apply blocking_shift_rev; auto.
(*====================================================*)
Qed.

 
