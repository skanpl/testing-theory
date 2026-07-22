

(*--------------a bunch of imports--------------------*)
From Stdlib Require Export Program.Equality .
From stdpp Require Export gmap.
From TestingTheory Require Export Must VACCS_Good gLts InteractionBetweenLts ActTau.
Include VACCS_Testing.


From TestingTheory Require Export DefinitionAS Convergence Termination.

Require Export List.
Require Export stdpp.base.
 

Require Export ForwarderConstruction.
(*---------------- notations -------------------------*)
Notation wt := WeakTransitions.wt.
Notation tau p := (g (𝛕 • p)).  
Notation inp x p := (g (gpr_input x p)).

Notation Linp c v :=  ( ActTau.ActExt (InputOutputActions.ActIn (c ⋉ v)) ).
Notation Lout c v := ( ActTau.ActExt (InputOutputActions.ActOut (c ⋉ v))  ).
Notation Ltau := ActTau.τ.
Notation sub t1 x1 :=  (subst_in_proc 0 x1 t1).


Notation ash mu :=  (VarC_action_add 1 mu). (*ash=action shift*)
Notation alpha := (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ). (*abstraction on a mu*)
Notation Alpha := (Subset_Act.map_set alpha). (*abstraction on a set of mus*)

(*---------------------------------------------------*)


Hint Constructors lts :mdb.



Lemma inv_mu: forall mu:InputOutputActions.ExtAct TypeOfActions,
  exists x v, ( ActExt mu = Linp x v) \/  
              (ActExt mu = Lout x v)   .
Proof.
intros; destruct mu,a; eauto.
Qed.



Lemma mu_impl_wt: forall p q mu, lts p (ActExt mu) q ->  
  wt p [mu] q.
Proof.
intros ? ? ? Hp.  
eapply WeakTransitions.wt_act; eauto with mdb.
Qed.



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



Lemma delta_id: forall pmu,
  𝝳ᴠᴀᴄᴄꜱ pmu = pmu.
Proof.
intro; destruct pmu,c; cbv; auto.
Qed.



Lemma extend_to_stable: forall p,
  p⤓ -> exists p', 
  wt p [] p' /\  (forall q, lts p' Ltau q -> False).  
Proof.
intros ? Hter.
dependent induction Hter.
set (decp:= proc_stable_dec p Ltau).
destruct decp as [decp| decp];
unfold proc_stable in decp; cbn in decp.
- exists p; split; eauto with mdb.
  intros p' Hlt. 
  set (lem:= lts_set_tau_spec1 _ _ Hlt).
  set_solver.
- set (empdec:= set_choose_or_empty (lts_set_tau p)).
  destruct empdec as [empdec|empdec]; try set_solver.
  destruct empdec as [p' Hlt].
  apply lts_set_tau_spec0 in Hlt.
  specialize (H0 _ Hlt). 
  destruct H0 as [q [Hwt Href]].
  eauto with mdb.
Qed.


Lemma extend_to_stable_trace: forall p p0 s,
  p⇓s -> wt p s p0 -> exists p', 
  wt p s p' /\  (forall q, lts p' Ltau q -> False).  
Proof.
intros ? ? ? Hcnv.
dependent induction Hcnv; eauto using extend_to_stable. 
intro Hwt; replace (μ :: s) with ([μ]++s) in Hwt; auto.
apply WeakTransitions.wt_split in Hwt.
destruct Hwt as [q [Hp Hq]].
specialize (H1 _ Hp Hq); destruct H1 as [p' [Hq2 Href]].
set (lem:= WeakTransitions.wt_concat _ _ _ _ _ Hp Hq2); 
eauto.
Qed.
