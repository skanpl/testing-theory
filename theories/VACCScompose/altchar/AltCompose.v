

Require Import AltGenerality.







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
  
  (****  preuve de 
         R(x?(y).p)⊆R(x?(y).q )*****)
   clear  Hwt Href Hcnv Hplq.
   intro. intro. 
   destruct H as [mu [G1 G2]]; subst. 
   exists mu.  
   split. 
   + destruct G1 as [mu0 [G1 [G2 G3]]].
     unfold "blocking", non_blocking in *.
     (*cbn in *.*)
     unfold non_blocking_output, InputOutputActions.is_output in *.
     destruct (inv_mu mu) as  [c [v inv_mu]].
     destruct inv_mu as [inv_mu|inv_mu].
     * inversion inv_mu; subst. clear inv_mu.
       destruct (inv_mu mu0) as  [c0 [v0 inv_mu0]].
       destruct inv_mu0 as [inv_mu0|inv_mu0]; subst.
       inversion inv_mu0; subst; cbv in G2; try (exfalso; auto).
       inversion inv_mu0; subst; cbv in G2; inversion G2; subst.
       set_solver.
     * exfalso; apply G3.
       exists (act c v); inversion inv_mu; auto.
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
Qed.


Proposition alt_comp_inp: forall x p q,
  (forall v, sub p v ≼ₐₛ sub q v) -> inp x p ≼ₐₛ inp x q. 
Proof.
unfold "≼ₐₛ"; intros ? ? ? Hplq; split;
try eapply lcnv_comp_inp; try eapply lacc_comp_inp; apply Hplq.
Qed.


(*=================   sum   ======================*)







Notation sum p q := (gpr_choice p q).

(* ----  weak transitions ----------*)
Lemma wt_sum: forall p q r mu s, 
  wt (g (sum p q)) (mu::s) r -> 
  wt (g p) (mu::s) r \/ wt (g q) (mu::s) r.
Proof.
intros ? ? ? ? ? Hwt. 
inversion Hwt; inversion l; eauto with mdb.
Qed.

Lemma wt_sumL_rev: forall p q r mu s,
  wt (g p) (mu::s) r -> wt (g (sum p q)) (mu::s) r.
Proof.
intros ? ? ? ? ? Hwt; inversion Hwt; subst.
- econstructor. econstructor. apply l. apply w.
- eapply WeakTransitions.wt_act; eauto.
  constructor; auto.
Qed.


Lemma wt_sumR_rev: forall p q r mu s,
  wt (g q) (mu::s) r -> wt (g (sum p q)) (mu::s) r.
Proof.
intros ? ? ? ? ? Hwt; inversion Hwt; subst.
- econstructor. apply lts_choiceR. apply l. apply w.
- eapply WeakTransitions.wt_act; eauto.
  apply lts_choiceR; auto.
Qed.


Lemma wt_summu: forall p q r mu, 
  wt (g (sum p q)) [mu] r -> 
  wt (g p) [mu] r \/ wt (g q) [mu] r.
Proof.
auto using wt_sum.
Qed.

Lemma wt_summuL_rev: forall p q r mu,
  wt (g p) [mu] r -> wt (g (sum p q)) [mu] r.
Proof.
auto using wt_sumL_rev.
Qed.


Lemma wt_summuR_rev: forall p q r mu,
  wt (g q) [mu] r -> wt (g (sum p q)) [mu] r.
Proof.
auto using wt_sumR_rev.
Qed.



Lemma wt_sumnil: forall p q r, 
  wt (g (sum p q)) nil r -> 
  r = sum p q  \/  wt (g p) nil r \/ wt (g q) nil r.
Proof.
intros ? ? ? Hwt.
inversion Hwt; try inversion l; eauto with mdb.
Qed.

(*------ convergence ----------*)

Lemma term_sum: forall p q,
  (g (sum p q)) ⤓ ->  (g p)⤓ /\ (g q)⤓. 
Proof.
intros ? ? Hsum; inversion Hsum.
 split; constructor; intros ? Hlt; apply H. 
- apply lts_choiceL; auto. 
- apply lts_choiceR; auto. 
Qed.

Lemma term_sum_rev: forall p q,
  (g p)⤓ -> (g q)⤓ -> (g (sum p q)) ⤓ . 
Proof.
intros ? ? Hp Hq.
constructor; intros ? Hsum; inversion Hsum; 
try inversion l; auto.
- apply Hp; auto.
- apply Hq; auto.
Qed.

Lemma cnv_sum: forall p q s,
  (g (sum p q))⇓s ->  (g p)⇓s /\ (g q)⇓s .
Proof.
intros ? ? ? Hcnv.
destruct s; inversion Hcnv; split; constructor; subst;  
try ( first 
  [set (lem:= term_sum p q H)| 
   set (lem:= term_sum p q H2)]; 
destruct lem); auto; intros ? Hwt; inversion Hcnv; apply H7. 
- apply wt_summuL_rev; auto.
- apply wt_summuR_rev; auto.
Qed.

Lemma cnv_sum_rev: forall p q s,
  (g p)⇓s -> (g q)⇓s -> (g (sum p q))⇓s.
Proof.
intros ? ? ? Hpcnv Hcnvq; destruct s; constructor; 
inversion Hpcnv; inversion Hcnvq; auto using term_sum_rev.
intros ? Hwt; apply wt_summu in Hwt; destruct Hwt; auto.
Qed.

Lemma lcnv_comp_sum: forall p q,
  g p ≼₁ g q ->  (g (sum p q))  ≼₁ (g (sum p q)) . 
Proof.
unfold "≼₁"; intros ? ? Hplq ? Hsum.
apply cnv_sum in Hsum; destruct Hsum; 
apply cnv_sum_rev; auto.
Qed.




(*
Lemma blah: forall p a,
  lts_set p a ≠ ∅ -> exists p', lts p a p'.
Proof.
intros.
destruct a.
Focus 2.
cbn in H.
*)


