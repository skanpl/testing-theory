Require Import Must.
Require Import VACCS_Instance .


From Must Require Import InputOutputActions ActTau OldTransitionSystems Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.

Notation "p << q" := (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p q) (at level 40).
Notation tauact q := (t • q).




Proposition ctx_compose_tau: forall p q, p << q -> 
  (g (gpr_tau p)) << (g (gpr_tau q)).
Proof.
intros p q Hmust.  
unfold "<<" in *.
intros e Hmp.
(*generalize dependent q.*) 
induction Hmp.  
- eauto with mdb. 
- (*intros q Htest.*) destruct ex as [r trans]. 
  inversion trans;subst.
  + eauto with mdb. 
  + eapply m_step; eauto with mdb.
    * eexists. do 2 constructor.
    * intros p' Htau.
      clear H1 com pt H.
      specialize (et _ l). specialize (H0 _ l).
      inversion Htau. subst.    
      admit. 


    * intros p' e' μ1 μ2. 
      intros Hpi Hmu1 Hmu2.
      clear pt H.
      specialize (et _ l). specialize (H0 _ l).
      admit.


      
  + eapply m_step; eauto with mdb.
    * eexists. do 2 constructor. 
    * clear pt H et H0.
      intros p' Htau.
      inversion Htau. subst.
      admit.
    * intros. 
      clear pt H et H0.
      admit.
Admitted.







(*
Require Import Coq.Program.Equality.

Proposition ctx_compose_tau2: forall p q, p << q -> 
  (g (gpr_tau p)) << (g (gpr_tau q)).
Proof.
intros p q Hmust.  
unfold "<<" in *.
intros e Hmp.
(*generalize dependent q.*) 
dependent induction Hmp.  
- eauto with mdb. 
- destruct ex as [r trans]. 
  inversion trans;subst.
  + clear H1 com H0 et H.
     
  + clear H1 com H pt.  
    eapply m_step; eauto with mdb.
    * eexists. do 2 constructor.
    * intros p' Htau.
      specialize (et _ l). specialize (H0 _ l).    
      admit. 
    * admit.

  + eapply m_step; eauto with mdb.
    * eexists. do 2 constructor. 
    * admit.
    * intros. 
      clear pt H et H0.
      admit.
Admitted.
    
*)        
    

