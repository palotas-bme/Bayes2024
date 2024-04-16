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