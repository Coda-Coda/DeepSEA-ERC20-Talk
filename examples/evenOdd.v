Definition Even (n1 : nat) := exists m1, n1 = 2 * m1.
Definition Odd  (n2 : nat) := exists m2, n2 = 2 * m2 + 1.

Lemma EvenToOdd : forall (n : nat), Even n -> Odd (n + 1).
Proof.
  intros.
  unfold Even in H.
  destruct H as [m1].
  unfold Odd.
  exists m1.
  rewrite <- H.
  reflexivity.
Qed.