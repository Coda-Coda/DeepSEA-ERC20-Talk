Require Import Nat.
Require Import PeanoNat.
Require Import Bool.
Require Import List.
Import ListNotations.

(* An example of a Coq proof involving lists *)
Print list.
(* Inductive list (A : Type) : Type :=
	|  nil : list A 
  | cons : A -> list A -> list A. *)

Fixpoint contains (n:nat) (l:list nat) : bool :=
  match l with
  | [] => false
  | h :: tl => (n =? h) || contains n tl
end.

Lemma contains_property :
  forall n list1, contains n list1 = true
    -> forall list2, contains n (list1 ++ list2) = true.
Proof.
  intros n.  
  induction list1.
  - simpl. intros. discriminate.
  - intros. simpl in *.
    apply orb_prop in H.
    destruct H.
    + apply orb_true_intro.
      left. assumption.
    + apply orb_true_intro.
      right.
      eapply IHlist1 in H.
      eassumption. 
Qed.
      
  

Lemma contains_correctness : forall n l, contains n l = true <-> In n l.
Proof.
  Print In.
  split.
  - induction l as [|l'].
    + simpl. discriminate.
    + simpl. intros.
      apply orb_prop in H.
      destruct H.
      * left. rewrite Nat.eqb_eq in H. auto.
      * right. apply IHl in H. assumption.
  - induction l as [|l'].
    + simpl. contradiction.
    + simpl. intros.
      destruct H.
      * apply orb_true_intro.
        left.
        subst.
        apply Nat.eqb_refl.
      * apply orb_true_intro.
        right.
        auto.
Qed.
     
intros.


(* Abandoned ideas: *)
(* 
Fixpoint removeDuplicates (l : list nat) : list nat :=
  match l with
  | [] => []
  | mem

Fixpoint sumlist (l : list nat) : nat :=
  match l with
  | [] => 0
  | h :: tl => h + sumlist tl
end.

Lemma sumlist  
*)