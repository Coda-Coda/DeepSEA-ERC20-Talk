:title: Provably Correct Smart Contracts using DeepSEA
:css: talk.css
:css: alectryon.css
:css: tango_subtle.css
:js-body: alectryon.js
:slide-numbers: true
:data-transition-duration: 0.01

.. :auto-console: true

----

==============================================
Provably Correct Smart Contracts using DeepSEA
==============================================

Daniel Britten
==============

Ethereum Engineering Group Meetup 2023
--------------------------------------

.. note::

  It's great to be here...

----

**Formal verification of programs**


E.g. theorem-proving for smart contracts correctness.

----

**Quick introduction to theorem-proving in Coq**

Example: Even and odd numbers

----

.. coq:: fold

  Definition Even (n : nat) := exists k, n = 2 * k.
  Definition Odd  (m : nat) := exists l, m = 2 * l + 1.
  
  Lemma EvenToOdd : forall (n : nat), Even n -> Odd (n + 1).
  Proof.
    intros.
    unfold Even in H.
    destruct H as [k].
    unfold Odd.
    exists k.
    rewrite <- H.
    reflexivity.
  Qed.

----

=======
DeepSEA
=======

----

================================
Modelling a Blockchain using Coq
================================

----

**References**

- Slides_ powered by Alectryon_: github.com/cpitclaudel/alectryon
- The DeepSEA compiler is partly based upon the CompCert_ Verified Compiler.

.. _Slides: https://github.com/Coda-Coda/Eth-Eng-Grp-Talk-2023
.. _Alectryon: https://github.com/cpitclaudel/alectryon
.. _CompCert: https://compcert.org/

----

=================
Additional Slides
=================

----

=================================================
Example: a property of a list membership function
=================================================

----

.. coq:: none

  Require Import Nat.
  Require Import PeanoNat.
  Require Import Bool.
  Require Import List.
  Import ListNotations.

.. coq:: fold

  Module MyList. (* .none *)
  Inductive list (A : Type) : Type :=
  | nil : list A 
  | cons : A -> list A -> list A.
  End MyList. (* .none *)

  Fixpoint contains (n:nat) (l:list nat) : bool :=
    match l with
    | [] => false
    | h :: tl => (n =? h) || contains n tl
  end.

----

.. coq:: fold

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

----

.. coq:: fold

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

----

=============================
Example: Simple state machine
=============================

----

.. image:: fsm-diagram-transparent.png
   :alt: example state machine diagram

----

.. coq:: none

  Require Import Coq.Program.Tactics.
  Local Obligation Tactic := idtac.

.. coq:: fold

  Inductive State :=
    | initial
    | middle
    | extra
    | final
  .

  Inductive Transition (before : State) :=
    | advance (prf : before <> final)
    | sidetrack (prf : before = initial).

----

.. coq:: fold

  Local Obligation Tactic := try discriminate. (* .none *)
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

----

.. coq:: fold

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

.. code:: coq

  Local Obligation Tactic := try discriminate. (* Used for the above. *)

----

.. coq:: fold

  Lemma three_transitions_gives_final : 
  forall t1 t2 t3, let s1 := step initial t1 in let s2 := step s1 t2 in
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
