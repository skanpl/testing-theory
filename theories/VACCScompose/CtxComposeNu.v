
(*---------- very temporary don't pay attention to this -------------------*)
Require Import Must.
Require Import VACCS_Instance .
From Must Require Import InputOutputActions ActTau OldTransitionSystems Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.
Notation "p << q" := (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p q) (at level 40).
Notation tau q := (t • q).
Notation sub t1 x1 := (t1 ^ x1).
Require Import Coq.Program.Equality.
(*-----------------------------------------------------------------------*)










(*============== admitted properties ================*)

Fixpoint shift (p:proc) : proc. Admitted.
Notation ash mu :=  (VarC_action_add 1 mu).

(*--------shift on lts -----------------*)
Lemma lts_shift_mu: forall (p q:proc) (mu:ExtAct TypeOfActions),
  lts p (ActExt mu) q -> lts (shift p) (ActExt ( ash mu)) (shift q).


Proof. 
Admitted.

Lemma lts_shift_tau: forall (p q:proc),
  lts p τ q -> lts (shift p) τ (shift q).


Proof. 
Admitted.

Lemma lts_shift_inv_tau: forall (p q:proc), lts (shift p) τ q -> 
  exists p', lts p τ p' /\ q = shift p'.

Proof. 
Admitted.

 
Lemma lts_shift_inv_mu: forall (p q:proc) (mu:ExtAct TypeOfActions), 
  lts (shift p) (ActExt mu) q -> 
  exists p' mu0, lts p (ActExt mu0) p' /\ q = shift p' /\ mu= ash mu0.

Proof. 
Admitted.

(*---------- shift  on dual predicate  --------------------*)
Lemma dual_shift: forall (mu1 mu2:ExtAct TypeOfActions),
  parallel_inter mu1 mu2 ->
  parallel_inter (ash mu1) (ash mu2).

Proof. 
Admitted.



Lemma dual_shift_inv: forall mu1 mu2, parallel_inter mu1 (ash mu2) ->
  exists mu0, mu1 = ash mu0 /\ parallel_inter mu0 mu2.

Proof. 
Admitted.
(*------------- other stuff --------------------------*)
	
Lemma ash_inj: forall (mu1 mu2:ExtAct TypeOfActions), 
  ash mu1 = ash mu2 -> mu1=mu2.

Proof. 
Admitted.



Lemma good_shift: forall (e:proc), 
  good_VACCS e <-> good_VACCS (shift e).

Proof. 
(*NB to prove this you need to generalize from shift to an 
  arbitrary substitution sigma because of lifting.
*) 
Admitted.




(*=========== new compose tentatives   ====================*)
 


Lemma mp_tonu: forall (p e: proc),
  p must_pass shift e -> ν p must_pass e.
Proof.
intros.
dependent induction H; eauto with mdb.
- eapply m_now; destruct (good_shift e); firstorder.
- eapply m_step.
  * destruct (good_shift e); clear pt H et H0 com H1 ex; firstorder.
  * destruct ex as [r trans]; inversion trans; subst.
    + eexists; do 2 constructor; eauto.
    + set (lem:= lts_shift_inv_tau _ _ l); destruct lem as [e0 [G1 G2]]; 
      eexists; eapply ParRight; eauto.
    + set (leme:= lts_shift_inv_mu _ _ _ l2).
      destruct leme as [e' [mu0 [He [b2eq mu2eq]]]]; subst.
      set (lem:= dual_shift_inv _ _ eq).
      destruct lem as [mu1 [mu1eq Hpi12]]; subst.
      eexists; eapply ParSync; eauto.
      constructor; eauto.
  * intros P Hnup.    
    inversion Hnup; subst; eauto.
  * intros e' He.
    eapply H0; try eapply lts_shift_tau; eauto.
  * intros P e' ? ? Hpi Hnup He.
    set (lem:= dual_shift _ _ Hpi). 
    inversion Hnup; subst.
    eapply H1; try apply lem; try eapply lts_shift_mu ; eauto.
Qed.




(*the only thing left to show in the following lemma is to show that
 a synchro between p and (shift e) preserve the must predicate.
*)
Lemma mp_fromnu: forall (p e: proc),
  ν p must_pass e -> p must_pass shift e.
Proof.
intros.
dependent induction H; eauto with mdb.
- eapply m_now; destruct (good_shift e); firstorder.
- eapply m_step.
  * destruct (good_shift e); clear pt H et H0 com H1 ex; firstorder.
  * destruct ex as [r trans]; inversion trans; subst.
    + inversion l; subst; eexists; constructor; eauto.
    + eexists; eapply ParRight; set (lem:= lts_shift_tau _ _ l); eauto.
    + inversion l1; subst. set (lem:= lts_shift_mu _ _ _ l2);
      eexists; eapply ParSync; try eapply dual_shift; eauto.
  * intros p' Hp.
    (*je m'étais fait avoir par le parsing de Rocq,je pensais que H se lisait:
       H : forall p' : proc, (ν p) ⟶ p' -> 
          (forall p : proc, p' = ν p) ->  p must_pass shift e   
           ^^^^^^^^^^^^^^^^^^^^^^^^^^
    mais enfaite ca se lit:
       H : forall p' : proc, (ν p) ⟶ p' -> 
          (forall p : proc, p' = ν p -> p must_pass shift e )
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      du coup je pensait etre coincé mais enfaite non, my bad *)

    eapply H; try constructor; eauto.
  * intros e' Hse.
    set (lem:= lts_shift_inv_tau _ _ Hse).
    destruct lem as [e1 [He Heeq]]; subst; eauto.

  * intros p' E ? ? Hpi Hp Hse. (*here, the goal is to show that a synchro*)
    cbv in Hpi.                 (*between p and (shift e) preserves must*)
    destruct μ1,μ2,a0; subst; try (exfalso; apply Hpi).
    + destruct c.  
      
      Print ChannelData. (*why is a channel either a cstC or bvarC  ??? *)
      (*wouldn't it be more reasonable to have 
        the type channel to be a 1-constructor ADT:
        Inductive channel := 
        | ch (n: nat) .  
        where n is a De Bruijn index ?
      *) 
   


      (* let's  say that we have
         Inductive channel := 
         | ch (n: nat) .  
         now to proceed in the proof we do a case analysis on n.
         [if n=0]: we would have 
           Hse: (shift e) ⟶[ActOut ((ch 0) ⋉ d)] E
           so by lts_shift_inv_mu (modulo some details), we have
               e ⟶[bla] _     /\    (ch 0) ⋉ d = ash bla   
           ("ash" means "action shift")
           in particular ch 0 = ch (... +1). impossible.
        
         [if n=k+1]: we would have
            Hp : p ⟶[ActIn (ch (k+1) ⋉ d)] p'
            Hse: (shift e) ⟶[ActOut ((ch (k+1)) ⋉ d)] E
           hence
             Hp : p ⟶[ash (ActIn ((ch k) ⋉ d)) ] p' 
             Hse: (shift e) ⟶[ ash (ActOut ((ch k) ⋉ d)) ] E
           now, 
             with Hp, we get: 
                 (ν p) ⟶[ActIn ((ch k) ⋉ d)]  (ν p')

             and with  lts_shift_in_mu, we get:
                 e ⟶[bla] e'   /\ E= shift e' /\ ash (ActOut ((ch k) ⋉ d)) = ash bla.
             so we also have by ash_inj:
                  ActOut ((ch k) ⋉ d)=bla
             hence we get the following fully dual transitions:
                   e ⟶[ActOut ((ch k) ⋉ d)] e'
                   (ν p) ⟶[ActIn ((ch k) ⋉ d)]  (ν p')
             Hence by H1 we get as desired:   
               p' must_pass shift e'             
               
          -------------
          so basically the idea behind the argument is that:
          p and e communicate along a channel c and we distinguish two case:  
            (1)   c is the restricted channel 
                        or 
            (2)   c is not the restricted channel.
         in case (1): 
            by definition of ((ν c) p)⟶[μ] _ , 
            the communication between p and e along c is 
            impossible so we conclude by exfalso.
         in case (2):
            p and e communicate along c which is not the restricted channel so
            everything is ok and we can conclude by induction hypo.
      *) 
      admit.  
Admitted.       





Proposition  ctx_compose_nu: forall (p q: proc),
  p << q -> (ν p) << (ν q). 
Proof.
unfold "<<"; intros.
set (lem:= mp_fromnu _ _ H0); 
set (lem2:= H _ lem);
set (lem3:= mp_tonu _ _ lem2); auto.
Qed.





