
Require Import DefinitionAS.
Require Import VACCS_Instance.

Require Import Termination.
Require Import Convergence.
Require Import WeakTransitions.


Hint Constructors proc gproc cnv terminate lts:db.



Lemma term_input: forall p  c, 
  terminate p -> terminate (g (gpr_input c p)) .
Proof.
intros.   
inversion H.   
eapply tstep.  
intros. 
inversion H1.
Qed.

Lemma term_input_rev: forall p  c, 
  terminate (g (gpr_input c p)) ->terminate p .
Proof.
intros.    
inversion H.   
eapply tstep.  
intros. 

Qed.


(*Print HintDb bla.*)

(*
Lemma term_input_rev: forall p  c, 
  terminate (g (gpr_input c p)) -> terminate p .
Proof.
intros.
inversion H. 
eapply tstep.
intros. 
inversion H1;subst .
eapply tstep.
intros.
*)



Proposition bla: forall s c p,
  (g (gpr_input c p)) ⇓ s -> p ⇓ s.
Proof.
intro.
induction s; intros.
- eapply cnv_nil.
  inversion H. subst.
  set (H1:= term_input (gpr_input c p)). 
  


Proposition input_compose: forall c p q,
  p ≼ₐₛ q -> 
  g (gpr_input c p)  ≼ₐₛ g (gpr_input c q).
Proof.
intros. 
unfold bhv_pre in *.
split.
unfold "≼₁".
induction s. 
- intro. (*case s=ε*)
  eapply Convergence.cnv_nil.
  eapply tstep.
  intros.
  inversion H1.
- intro. (*case s=a.s*) 
  eapply cnv_act.
  * destruct H as [G1 G2].
    unfold "≼₁" in G1.
    inversion H0. subst.
    eapply tstep.
    intros.  
    inversion H.
  * intros.
    inversion H0. subst.
    specialize (H6 q0).
    apply H6.
    eapply wt_act.
    inversion H1. subst. inversion l.
    subst. 
    destruct H as [G1 G2].
    unfold "≼₁" in G1.




    

Print cnv.

 H : gLts.lts_step (gpr_input c q) ActTau.τ q0
