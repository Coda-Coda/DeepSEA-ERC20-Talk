Require Import Coq.Program.Tactics.
Local Obligation Tactic := idtac.

(* An example involving a simple state machine *)

Inductive State :=
  | initial
  | one
  | two
  | extra
  | final
.

Inductive Transition (before : State) :=
  | advance (prf : before <> final)
  | sidetrack (prf : before = one).

Local Obligation Tactic := try discriminate.
Program Definition step (s : State) (t : Transition s) :=
  match t with
  | advance _ _ =>
    match s with
    | initial => one
    | one => two
    | two => final
    |  extra => two
    | final => _
    end
  | sidetrack _ _ =>
    match s with
    | one => extra
    | _ => _
    end
end.
Next Obligation.
intros.
exfalso.
subst.
contradiction.
Defined.
Next Obligation.
intros.
exfalso.
subst.
contradiction.
Defined.

Lemma four_transitions_gives_final : 
  forall t1 t2 t3 t4,
  let s1 := step initial t1 in
  let s2 := step s1 t2 in
  let s3 := step s2 t3 in
  step s3 t4 = final.
Proof.
  intros.
  destruct t1. simpl in *.
  destruct t2. simpl in *.
  destruct t3. simpl in *.
  destruct t4.
    contradiction.
    discriminate.
  discriminate.
  simpl in *.
  destruct t3. simpl in *. destruct t4. simpl in *. reflexivity. discriminate.
  discriminate.
  discriminate.
Qed.
