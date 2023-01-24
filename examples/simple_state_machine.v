Require Import Coq.Program.Tactics.
Local Obligation Tactic := idtac.

(* An example involving a simple state machine *)

Inductive State :=
  | initial
  | middle
  | extra
  | final
.

Inductive Transition (before : State) :=
  | advance (prf : before <> final)
  | sidetrack (prf : before = initial).

Local Obligation Tactic := try discriminate.
Program Definition step (s : State) (t : Transition s) :=
  match t with
  | advance _ _ =>
    match s with
    | initial => middle
    | middle => final
    | extra => middle
    | final => _
    end
  | sidetrack _ _ =>
    match s with
    | initial => extra
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

Lemma three_transitions_gives_final : 
  forall t1 t2 t3,
  let s1 := step initial t1 in
  let s2 := step s1 t2 in
  step s2 t3 = final.
Proof.
  intros.
  destruct t1. simpl in *.
    - destruct t2. simpl in *.
      + destruct t3.
        * contradiction.
        * discriminate.
      + discriminate. 
    - destruct t2. simpl in *.
        + destruct t3. simpl in *.
          * reflexivity.
          * discriminate.
        + discriminate.
Qed.
