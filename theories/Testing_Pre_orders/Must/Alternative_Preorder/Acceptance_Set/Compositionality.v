
Require Import DefinitionAS.
Require Import VACCS_Instance.

Require Import Termination.
Require Import Convergence.
Require Import WeakTransitions.


Hint Constructors proc gproc cnv terminate lts:db.

Notation sub p v := (p^v).

Lemma term_input: forall p  c, 
  terminate p -> terminate (g (gpr_input c p)) .
Proof.
intros.   
inversion H.    
eapply tstep.  
intros.  
inversion H1.
Qed.



(*
Lemma term_input_rev: forall p  c, 
  terminate (g (gpr_input c p)) ->terminate p .
Proof.
intros.    
inversion H.   
eapply tstep.  
intros. 
clear H0.






Proposition bla: forall s c p,
  (g (gpr_input c p)) ⇓ s -> p ⇓ s.
Proof.
intro.
induction s; intros.
- eapply cnv_nil.
  inversion H. subst.
  set (H1:= term_input (gpr_input c p)). 
*)
  


Proposition input_compose: forall c p q,
  p ≼ₐₛ q -> 
  g (gpr_input c p)  ≼ₐₛ g (gpr_input c q).
Proof.
intros. 
unfold bhv_pre in *.
split.
unfold "≼₁".
+ induction s. 
  - intro. (*case s=ε*)
    eapply Convergence.cnv_nil.
    eapply tstep.
    intros.
    inversion H1. 
  - intro. (*case s=a.s*)  
    eapply cnv_act.
    * constructor. intros. inversion H1.
    * intros. inversion H0. subst.
      
      assert (exists v, q0= sub p v).
      inversion H1. subst.inversion l.
      inversion l. subst.
      assert (sub q v = q0). 
      inversion w. auto. subst.
      

Admitted.
 
