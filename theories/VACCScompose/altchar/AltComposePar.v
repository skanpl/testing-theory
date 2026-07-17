

Require Import AltGenerality.






(*------------weak transitions -------------*)
Lemma wt_parL: forall p p' q s, 
  wt p s p' -> wt (p ‖ q) s (p' ‖ q).
Proof.
intros ? ? ? ? Hwt.
dependent induction Hwt; eauto with mdb.
- eapply WeakTransitions.wt_tau; try eapply lts_parL; eauto.
- eapply WeakTransitions.wt_act; try eapply lts_parL; eauto.
Qed.

Lemma wt_parR: forall p q q' s, 
  wt q s q' -> wt (p ‖ q) s (p ‖ q').
Proof.
intros ? ? ? ? Hwt.
dependent induction Hwt; eauto with mdb.
- eapply WeakTransitions.wt_tau; try eapply lts_parR; eauto.
- eapply WeakTransitions.wt_act; try eapply lts_parR; eauto.
Qed.

Lemma wt_invpar: forall p q s Q, 
  wt (p‖q) s Q -> exists p' q', Q=p'‖q'.
Proof. 
intros ? ? ? ? Hwt; dependent induction Hwt; eauto;
inversion l; subst; eapply IHHwt; eauto.
Qed.
(*-------------- convergence ------------------*)
Lemma term_parL: forall p q,  (p‖q)⤓ -> p⤓ .
Proof.
intros ? ? H.
dependent induction H; constructor.
intros p' Hp.
eapply H0; constructor; auto.
Qed.

Lemma term_parR: forall p q,  (p‖q)⤓ -> q⤓ .
Proof.
intros ? ? H.
dependent induction H; constructor.
intros p' Hp.
eapply H0; constructor; auto.
Qed.

Lemma cnv_parL: forall p q s, (p‖q)⇓s ->  p⇓s.
Proof.
intros ? ? ? Hcnv.
dependent induction Hcnv; constructor; eauto using term_parL.
intros p' Hwt.
eapply H1; eauto with mdb.
eauto using wt_parL.
Qed.

Lemma cnv_parR: forall p q s, (p‖q)⇓s ->  q⇓s.
Proof.
intros ? ? ? Hcnv.
dependent induction Hcnv; constructor; eauto using term_parR.
intros q' Hwt.
eapply H1; eauto with mdb.
eauto using wt_parR.
Qed.
(*-------------------------------------------*)

Notation vact := (InputOutputActions.ExtAct TypeOfActions).

(*
Inductive zip: trace vact -> trace vact -> trace vact -> Prop :=
| zip_nil: zip [] [] []
| zip_consL: forall s s1 s2 mu,
    zip s s1 s2 -> zip (mu::s) (mu::s1) s2 
| zip_consR: forall s s1 s2 mu,
    zip s s1 s2 -> zip (mu::s) s1 (mu::s2) 
| zip_consLR: forall s s1 s2 mu1 mu2,
    zip s s1 s2 -> dual mu1 mu2 -> 
    zip s (mu1::s1) (mu2::s2) 
.
*)

Inductive zip: trace vact -> trace vact -> trace vact -> Prop :=
| zip_nil: zip [] [] []
| zip_consL: forall s s1 s2 mu,
    zip s s1 s2 -> zip (mu::s) (mu::s1) s2 
| zip_consR: forall s s1 s2 mu,
    zip s s1 s2 -> zip (mu::s) s1 (mu::s2) 
| zip_consLR: forall s s1 s2 mu1 mu2,
    zip s s1 s2 -> dual mu1 mu2 -> 
    zip s (mu1::s1) (mu2::s2) 
.

Hint Constructors zip:mdb.



Lemma zip_idL: forall s, zip s s [].
Proof. 
induction s; eauto with mdb.
Qed.

Lemma zip_idR: forall s, zip s [] s.
Proof. 
induction s; eauto with mdb.
Qed.

Lemma dual_commut: forall mu1 mu2, 
  dual mu1 mu2 -> dual mu2 mu1.
intros.
destruct mu1,mu2,a,a0; cbn; eauto with mdb.
Qed.


Lemma zip_commut: forall s s1 s2, 
  zip s s1 s2 -> zip s s2 s1.
Proof.
intros ? ? ? Hzip; induction Hzip; eauto with mdb.
apply zip_consLR; eauto using dual_commut.
Qed.


Notation Aout c v := (InputOutputActions.ActOut (c ⋉ v)).
Notation Ainp c v := (InputOutputActions.ActIn (c ⋉ v)).


Lemma zip_wt: forall (p q p' q':proc) s,
  wt (p‖q) s (p'‖q')  -> exists s1 s2, 
  zip s s1 s2 /\ wt p s1 p' /\  wt q s2 q'. 
Proof.
intros ? ? ? ? ? Hwt. 
dependent induction Hwt.
- exists [],[]; eauto with mdb.
- inversion l; subst; 
  specialize (IHHwt _ _ _ _ eq_refl eq_refl);
  destruct IHHwt as [s1 [s2 [Hzip [Hw1 Hw2]]]].
  + exists ((Aout c v)::s1),
           ((Ainp c v)::s2).
    repeat split; inversion Hwt; subst; try eapply zip_consLR; 
    try apply zip_nil; cbn; eauto with mdb.
  + exists ((Ainp c v)::s1),
           ((Aout c v)::s2).
    repeat split; inversion Hwt; subst; try eapply zip_consLR; 
    try apply zip_nil; cbn; eauto with mdb.
  + eexists; eauto with mdb.
  + eexists; eauto with mdb.
- inversion l; subst; 
  specialize (IHHwt _ _ _ _ eq_refl eq_refl);
  destruct IHHwt as [s1 [s2 [Hzip [Hw1 Hw2]]]].
  + exists (μ::s1),s2; eauto with mdb.
  + exists s1,(μ::s2); eauto with mdb.
Qed.


Lemma wt_compose_par: forall p q p' q',
  wt p [] p' -> wt q [] q' -> 
  wt (p‖q) [] (p'‖q').
Proof.
intros ? ? ? ? Hp.
dependent induction Hp; intros Hq; inversion Hq; 
eauto with mdb; subst.
eauto using wt_parR. 
eapply WeakTransitions.wt_tau; try eapply lts_parL; eauto.
eapply WeakTransitions.wt_tau; try eapply lts_parL; eauto.
Qed.


Lemma lts_com: forall p p' q q' mup muq, 
  lts p (ActExt mup) p' -> lts q (ActExt muq) q' -> 
  dual mup muq ->
  lts (p‖q) Ltau (p'‖q').
Proof.
intros ? ? ? ? ? ? Hp Hq Hdual.
set (lemp:= inv_mu mup); set (lemq:= inv_mu muq).
destruct lemp as [x [vx lemp]]. 
destruct lemq as [y [vy lemq]].
destruct lemp,lemq; inversion H0; inversion H; subst; 
cbn in *; try (exfalso; apply Hdual); 
inversion Hdual; subst; eauto with mdb.
Qed.
(*
Lemma wt_cancel: forall p q p' q' mup muq sp sq,
  wt p (mup::sp) p' -> wt q (muq::sq) q' -> 
  dual mup muq -> 
  wt (p‖q) (sp++sq) (p'‖q').
Proof.
intros ? ? ? ? ? ? ? ? Hp Hq Hdual.
inversion Hp; inversion Hq; subst. 
- admit.
- admit.
- admit.
- set (lem:= lts_com _ _ _ _ _ _ l l0 Hdual).
*) 



Lemma wt_parmerge: forall p q p' q' sp sq,
  wt p sp p' -> wt q sq q' -> 
  wt (p‖q) (sp++sq) (p'‖q').
Proof.
intros ? ? ? ? ? ? Hp.
dependent induction Hp; intros Hq; 
cbn in *; try specialize (IHHp Hq). 
- eauto using wt_parR.
- eapply WeakTransitions.wt_tau; 
  try eapply lts_parL; eauto.
- eapply WeakTransitions.wt_act; 
  try eapply lts_parL; eauto.
Qed.
 


Lemma wt_cancel_later: forall q q' p p' mup muq s,
  lts p (ActExt mup) p' -> wt q (muq:: s) q'-> 
  dual mup muq ->
  wt (p‖q) s (p'‖q').
Proof.
intros ? ? ? ? ? ? ? Hlt Hwt Hdual.
dependent induction Hwt.
- eapply WeakTransitions.wt_tau; 
  try eapply lts_parR; eauto.
- set (lem1:= lts_com _ _ _ _ _ _ Hlt l Hdual).
  set (lem2:= wt_parR p' _ _ _ Hwt).
  eauto with mdb.
Qed.

 


Lemma wt_eventually: forall p p' mu,
 wt p [mu] p' ->  exists p1 p2,
 wt p [] p1  /\ lts p1 (ActExt mu) p2 /\ wt p2 [] p'.
Proof.
intros.
dependent induction H.
- specialize (IHwt _ JMeq_refl).
  destruct IHwt as [p1 [p2 [Hq [Hlt Hp2]]]].
  exists p1,p2; repeat split; auto.
  eapply WeakTransitions.wt_tau; eauto.
- exists p,q; eauto with mdb.
Qed.

Lemma wt_cancel: forall p q p' q' mup muq sp sq,
  wt p (mup::sp) p' -> wt q (muq::sq) q' -> 
  dual mup muq -> 
  wt (p‖q) (sp++sq) (p'‖q').
Proof.
induction sp.
- intros; cbn.
  inversion H; subst.
  + set (lem:= wt_eventually _ _ _ H).
    destruct lem as [p1 [p2 [Hp [Hlt Hp2]]]].
    set (lem:= wt_cancel_later _ _ _ _ _ _ _ Hlt H0 H1).
    set (lempar:= wt_parL _ _ q _ Hp).
    set (lempar2:= wt_parL _ _ q' _ Hp2). 
    set (lemconc:=  WeakTransitions.wt_concat  _ _ _ _ _ lempar lem).
    cbn in *.
    set (lemconc2:=  WeakTransitions.wt_concat  _ _ _ _ _ lemconc lempar2).
    replace (sq ++ []) with sq in lemconc2; try rewrite app_nil_r; auto. 
  + set (lem:= wt_cancel_later _ _ _ _ _ _ _ l H0 H1).
    set (lempar:= wt_parL _ _ q' _ w).  
    set (lemconc:= WeakTransitions.wt_concat _ _ _ _ _ lem lempar).
    replace (sq ++ []) with sq in lemconc; try rewrite app_nil_r; auto.
- intros ? Hp Hq Hdual; cbn.
 Admitted.




Lemma zip_wt_rev: forall (p q p' q':proc) s s1 s2,
  zip s s1 s2 -> wt p s1 p' ->  wt q s2 q' ->
  wt (p‖q) s (p'‖q'). 
Proof.
induction s; intros ? ? Hzip Hp Hq.
- inversion Hzip; subst.
  + inversion Hp; inversion Hq; subst;
    eauto using wt_parR; eauto using wt_parL;
    eauto using wt_compose_par.
  + 


- 






Lemma zip_wt_rev: forall (p q p' q':proc) s s1 s2,
  zip s s1 s2 -> wt p s1 p' ->  wt q s2 q' ->
  wt (p‖q) s (p'‖q'). 
Proof.
intros ? ? ? ? ? ? ? Hzip.
dependent induction Hzip; intros Hp Hq.
- inversion Hp; inversion Hq; subst; 
  eauto using wt_parR; eauto using wt_parL;
  eauto using wt_compose_par.
- 

  (*
  apply (wt_parL _ _ q) in Hp.
  apply (wt_parR p') in Hq.
  set (lem := WeakTransitions.wt_concat).
  specialize (lem _ _ _ _ _ Hp Hq); cbn in lem. 
  *)
 
destruct Hex as [s1 [s2 [Hzip [Hwtp Hwtq]]]].





    
(*
Lemma term_zip: forall p s1 s2,
  p⤓ -> zip [] s1 s2 -> p⇓s1.
Proof.
intros ? ? ? Hterm; induction Hterm.
intro Hzip; induction Hzip; eauto with mdb.
- destruct s1.
- 


Lemma cnv_zip: forall p s s1 s2, 
  p⇓s -> zip s s1 s2 -> p⇓s1.
Proof.
intros ? ? ? ? Hcnv Hzip; induction Hcnv; eauto with mdb.
- destruct s1,s2; inversion Hzip; subst; eauto with mdb.
  constructor; auto.
  intros p' Hwt. 
*)  







(*
(* gtrace= generalized trace *)
CoInductive gtrace {A:Type} :=
| gnil
| gcons (x:A) (xs:gtrace)  .

(* vact= visible action *)
Notation vact := (InputOutputActions.ExtAct TypeOfActions).
Notation "x :: xs" := (gcons x xs).        
Notation "[]" := gnil.        


(* tts= trace transition system *)
CoInductive tts: proc -> gtrace -> Prop :=
| tts_nil: forall p, tts p gnil
| tts_cons: forall p p' mu s, 
    lts p mu p' -> tts p' s -> tts p' (mu::s). 

CoInductive zip: gtrace -> gtrace -> gtrace -> Prop :=
| zip_nil: zip [] [] []
| zip_consL: forall s s1 s2 mu,
    zip s s1 s2 -> zip (mu::s) (mu::s1) s2 
| zip_consR: forall s s1 s2 mu,
    zip s s1 s2 -> zip (mu::s) s1 (mu::s2) 
| zip_consLR: forall s s1 s2 mu1 mu2,
    zip s s1 s2 -> dual mu1 mu2 -> 
    zip s (mu1::s1) (mu2::s2) 
.

(*
(* basically the definition of cnv but declared as coinductive*)
CoInductive gcnv: proc -> gtrace -> Prop :=
| cnv_nil : forall p,  p ⤓ -> gcnv p []
| cnv_act : forall p mu s,
    p ⤓ -> (forall q, wt p [mu] q -> gcnv q s) -> 
    gcnv p (mu::s).
Notation "p ⇓ s" := (cocnv p s).
*)
Hint Constructors  zip tts gtrace: mdb.


Lemma cocnv_parL: forall p q (s:gtrace), (p‖q)⇓s -> p⇓s.
Proof.
intros ? ? ? Hcocnv.

*)

