:title: Provably Correct Smart Contracts using DeepSEA
:css: talk.css
:css: alectryon.css
:css: tango_subtle.css
:js-body: alectryon.js
:slide-numbers: true
:data-transition-duration: 0.01
:alectryon/serapi/args: -R /home/daniel/Documents/Code/research/Eth-Eng-Grp-Talk-2023/contracts/result DeepSpec -R /home/daniel/Documents/Code/research/Eth-Eng-Grp-Talk-2023/contracts/Crowdfunding Crowdfunding -R /home/daniel/Documents/Code/research/Eth-Eng-Grp-Talk-2023/contracts/trivial trivial -R /home/daniel/Documents/Code/research/Eth-Eng-Grp-Talk-2023/contracts/proofs SmartContract

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

**Overall Goal:**
*Demonstate a technique for showing the correctness of smart contracts*

----

**Overview:**

- Theorem-proving example in the proof assistant Coq
- DeepSEA by example
- Modelling a blockchain
- Handling reentrancy
- A correctness property of a Crowdfunding contract

----

**Introduction to theorem-proving in Coq**

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

**Introduction to creating a DeepSEA smart contract**

Example: Trivial contract converting bool to int

----


.. code:: ocaml

  object signature trivial = {
      const boolToInt : bool -> int;
      boolToIntTracker : bool -> int
  }

  object Trivial : trivial {
      let seenTrueYet : bool := false

      let boolToInt b =
        if b then 1 else 0

      let boolToIntTracker b =
        if b then
          begin
              seenTrueYet := true;
              1
          end
        else 0
  }

  layer CONTRACT = { o = Trivial }

----

.. code:: bash

  $ dsc trivial.ds bytecode
  5b60005b60206109205101610920525b61022660006020610920510301525b60006020
  610920510301516101005260206101002060006020610920510301525b600060006020
  61092051030151555b60206109205103610920525b60005b9050386300000073600039
  386000f35b60006000fd5b610940610920527c01000000000000000000000000000000
  000000000000000000000000006000350480635192f3c01463000000495780631e01e7
  071463000000965760006000fd5b6004355b60006109205101610920525b8063000000
  67576300000085565b600190505b60006109205103610920525b805b90506000526020
  6000f35b60009050630000006c565b60006000fd5b6004355b60206109205101610920
  525b8063000000b4576300000111565b61022660006020610920510301525b60006020
  610920510301516101005260206101002060006020610920510301525b600160006020
  61092051030151555b600190505b60206109205103610920525b805b90506000526020
  6000f35b6000905063000000f8565b60006000fd

----

`$ dsc trivial.ds abi`

.. code:: json

  [ {"type":"constructor",
    "name":"constructor",
    "inputs":[], "outputs":[], "payable":false,
    "constant":false, "stateMutability":"nonpayable"},
  {"type":"function",
    "name":"boolToInt",
    "inputs":[{"name":"b", "type":"bool"}],
    "outputs":[{"name":"", "type":"uint256"}],
    "payable":false,
    "constant":true,
    "stateMutability":"view"},
  {"type":"function",
    "name":"boolToIntTracker",
    "inputs":[{"name":"b", "type":"bool"}],
    "outputs":[{"name":"", "type":"uint256"}],
    "payable":true,
    "constant":false,
    "stateMutability":"payable"}]

.. note::

  Next slide is a reminder of the contract definition.

----

.. code:: ocaml

  object signature trivial = {
    const boolToInt : bool -> int
  }
  
  object Trivial : trivial {
      let boolToInt b = if b then 1 else 0
  }
  
  layer CONTRACT  = {
      o = Trivial
  }

----

.. coq:: none

  Require Import trivial.DataTypeOps.
  Require Import trivial.LayerCONTRACT.

  Require Import DeepSpec.lib.Monad.StateMonadOption.
  Require Import DeepSpec.lib.Monad.RunStateTInv.
  Require Import lib.ArithInv.
  Import DeepSpec.lib.Monad.Monad.MonadNotation.

  Require Import Lia.
  Require Import List.
  Require Import Bool.
  Require Import ZArith.
  Require Import cclib.Maps.
  Require Import cclib.Integers.

  Require Import DataTypes.
  Require Import backend.MachineModel.

  Require Import DataTypes.
  Import ListNotations.

  Require Import core.MemoryModel. 
  Require Import HyperTypeInst.

  Require Import Maps.
  Import Maps.Int256Tree_Properties.
  Import Maps.Int256Tree.

  Require Import trivial.ContractModel.
  Import trivial.ContractModel.ContractModel.

  Open Scope Z.

  Section Proof.

.. coq:: unfold

  Print Trivial_boolToInt_opt.

----

.. coq:: unfold

  Print Trivial_boolToIntTracker_opt.

.. coq:: none

  End Proof.
  Open Scope nat.

----

**Refinement and the Lem EVM model**

----

================================
Modelling a Blockchain using Coq
================================

----

==========
Reentrancy
==========

----

===================================
A Crowdfunding Correctness Property
===================================

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
    | advance _ =>
      match s with
      | initial => middle
      | middle => final
      | extra => middle
      | final => _
      end
    | sidetrack _ =>
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
