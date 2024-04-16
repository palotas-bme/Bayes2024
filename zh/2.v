Lemma problem_1 : forall A B C : Prop, A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  intros.
  destruct H as [H1 H2].
  elim H2.
  intros.
  left.
  split.
  auto.
  auto.
  intros.
  right.
  auto.
Qed.
Lemma problem_2 : forall A B C : Prop, ((B -> A) /\ (C -> A)) -> ((B \/ C -> A)).
Proof.
  intros A B C H. 
  destruct H as [HBA HCA]. 
  intros [HB | HC]. 
  - apply HBA. 
    apply HB. 
  - apply HCA.
    apply HC.
Qed.
Lemma problem_3 : forall A B : Prop, (A \/ ~A) -> ((A -> B) -> A) -> A.
Proof.
firstorder.
Show Proof.
Qed.
Lemma problem_4 : forall (U : Type) (A B : U -> Prop), (exists x, A x /\ B x) -> (exists x, A x) /\ (exists x, B x).
Proof.
  intros U A B [x [HA HB]].
  split.
  - exists x.
    apply HA.
  - exists x.
    apply HB.
Qed.