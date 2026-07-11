

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



