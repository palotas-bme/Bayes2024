Lemma problem_4 : forall (U : Type) (A B : U -> Prop), (exists x, A x /\ B x) -> (exists x, A x) /\ (exists x, B x).
Proof.
  intros U A B [x [HA HB]].
  split.
  - exists x.
    apply HA.
  - exists x.
    apply HB.
Qed.