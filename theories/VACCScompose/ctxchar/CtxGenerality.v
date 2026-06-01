
Require Export Coq.Program.Equality.
Require Export VACCS.
Require Export VACCS_Instance.
Require Export VACCS.Congruence.
Require Export Must.
Include VACCS_congruence.




(*
Require Export InputOutputActions ActTau Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.
*)





(*================================================================================*)
(*/!\/!\/!\/!\/!\  How can i make this work???   /!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\*)

Locate proc.  (*what???*)
Lemma why: forall p e: proc,
  p must_pass e  -> True.
Proof.
(*/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\/!\*)
(*================================================================================*)



 





























(* Tactic that looks for lts/lts_step assumptions and inverts them to
  learn about the shape of the conclusion *)
(*
Ltac lts_inversion :=
try match goal with
| H : lts_step ?p ?a ?q |- _ =>
  solve[inversion H; subst; discriminate || tauto]
| H : lts ?p ?a ?q |- _ => inversion H; subst; discriminate || tauto
 end;
match goal with
| H : lts_step ?p ?a ?q |- _ => inversion H; subst; clear H
| H : lts ?p ?a ?q |- _ => inversion H; subst; clear H
 end.
*)





(*========= notations =====================*)

Notation "p << q" := (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p q) (at level 40).
Notation tau q := (𝛕 • q).
Notation sub t1 x1 := (t1 ^ x1).


Notation congs := cgr.



(*=========== cong preseves mp ===============*)
Lemma mp_congsL: forall p e r: proc,
  p must_pass e (*-> congs p r ->  r must_pass e *) -> True.
Proof.
intros. 
set (lem:= must_eq_server p r e).
specialize (lem H0); auto.
Qed. 

Lemma mp_congsR: forall p e r: proc,
  p must_pass e -> congs e r ->  p must_pass r.
Proof.
intros. 
set (lem:= must_eq_client p e r).
specialize (lem H0); auto.
Qed. 
(*========== other cong and << stuff  ============*)

Lemma mpless_congs: forall p q r: proc,
  p << q -> congs q r ->  
    p << r.
Proof.
unfold "<<"; intros.
specialize (H _ H1).
set (lem:= mp_congsL _ _ _ H H0); auto.
Qed.

Proposition mpless_trans: forall p q r:proc,
  p << q ->   q << r ->  
    p << r.
Proof.
unfold "<<"; auto.
Qed.

