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