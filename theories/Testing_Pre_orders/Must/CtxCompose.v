Require Import Must.
Require Import VACCS_Instance .


From Must Require Import InputOutputActions ActTau OldTransitionSystems Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.

Notation "p << q" := (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p q) (at level 40).
Notation tauact q := (t • q).


(*
Proposition ctx_compose_tau: forall p q, p << q -> 
  (g (gpr_tau p)) << (g (gpr_tau q)).
Proof.
intros p q Hmust.  
unfold "<<" in *.
intros e Hmp.
generalize dependent q. 
destruct Hmp.  
- eauto with mdb. 
- (*intros q Htest.*) destruct ex as [r trans]. 
  inversion trans;subst; intros.
  + inversion l; subst. intros.
    eapply m_step; eauto with mdb.
   *eexists. do 2 constructor.
   *intros p' Htau. inversion Htau. subst.
    eauto with mdb.
  * intros e' He.
    clear com. 
    specialize (et _ He). 
    specialize (pt _ l).
    (*             
            τ.a2  MP  e'
             ↓
             a2

     ==>   
             τ.a2  MP  e'
             ↓    MP
             a2
 
   thus:       ...
            —————————— 
             a2 MP e' 
           ————————————Hmust
            q MP e'


*)   
 
    assert (q must_pass e'). admit.
    admit.
 
  * admit. 

+ clear com.
  specialize (et _ l).
  tau.q MP
p MP e          tau.p MP b2
*)







Proposition ctx_compose_tau: forall p q, p << q -> 
  (g (gpr_tau p)) << (g (gpr_tau q)).
Proof.
intros p q Hmust.  
unfold "<<" in *.
intros e Hmp.
destruct Hmp.  
- eauto with mdb. 
- (*intros q Htest.*) destruct ex as [r trans]. 
  inversion trans;subst.
  inversion l; subst.
  eapply m_step; eauto with mdb.

  * eexists. do 2 constructor.
  * intros p' Htau. inversion Htau. subst.
    eauto with mdb.
  * intros e' He.
    clear com. 
    specialize (et _ He). 
    specialize (pt _ l).
    (* 
         

find something
==>   
            τ.q   MP  e
                      ↓
                      e'  

  ==>
            τ.q   MP  e
               MP     ↓
                      e'  

*)   
     admit. 
  * intros p' e' μ1 μ2 pi Htau He.
    inversion Htau.
  * 
    specialize (et _ l).
   (* 
        τ.p  MP  b2
         ↓    (MP)
         p

Hmust
==>

  q MP b2


==> ???

    *)
   (*
   (*======  bidouillage=========*)
   eapply m_step; eauto with mdb. 
   eexists. do 2 constructor.
   intros. inversion H. subst.
   clear com.
   specialize (pt p).
   eapply Hmust.
   eapply pt.
   constructor.

   intros e' He.
   clear com.
   Focus 2. intros. inversion H0. 
   (*==========================*)
  *)
   admit.
  * inversion l1.  

Admitted.
