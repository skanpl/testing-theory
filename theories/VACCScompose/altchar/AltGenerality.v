

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
