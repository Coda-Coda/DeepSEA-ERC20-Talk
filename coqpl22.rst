:title: Coq meets literate programming: Tools for documenting, preserving, and sharing mechanized proofs
:css: talk.css
:css: alectryon.css
:css: tango_subtle.css
:js-body: talk.js
:js-body: alectryon.js
:slide-numbers: true
:data-transition-duration: 0.01
:alectryon/serapi/args: -Q /home/clement/git/alectryon/talk/coq/ ""

.. :auto-console: true

----

.. container:: titlepage

   .

================================
 Coq meets literate programming
================================

Tools for documenting, preserving, and sharing mechanized proofs
================================================================

Clément Pit-Claudel
-------------------

CoqPL 2022
----------

.. note::

   Thanks for the introduction!  It's a real honor to be able to talk to you all today.  I'll prefix this by saying that this was work that was done while I was a student at MIT (and I'm interested in continuing once I move to EPFL, which is where I'll be teaching next year), but it's completely disconnected from what I do at my current employer AWS.

---

=====================
 A bit of background
=====================

.. note::

   This talk is about literate programming and Coq tools, but let me take a step back and give you a bit of context.
   At heart, I'm a programmer, and there's nothing that gives me more joy than building stuff.  And I find that the best motivation for building something is needing something.

----

TODO Synchronicity image from lifehacker
TODO CoverArt

.. note::

   Back in the day "needing something" meant building backup software and software to download album covers from my MP3 player for MP3 players.

---

TODO alarm clock / Rockbox

.. note::

   Later on, when I didn't get enough sleep because of too much time spent building tools, it meant building alarm clock software to wake up in the morning.  This was back in the days were MP3 players were a separate thing from phones and you carried them in separate pockets, and I programmed mine to wake up at a certain time and start playing music.

   That was, incidentally, one of my first times writing real C code.

---

TODO Rockbox patch

.. note::

   Spoiler, C is hard.  Back in the day I usually didn't go to bed before midnight, so it took me surprisingly long to realize that if you programmed the alarm for the next day it just didn't ring at all.

---

TODO end to end picture

.. note::

   I'd love to say that this is my origin story for doing formal verification and proofs, but I actually didn't come into contact with the Coq proof assistant until about 3 year later.  Since then I've mostly been a systems and compilers person, but amusingly most of my interactions with my community still revolve around tools, specifically tools for the Coq proof assistant.

---

TODO: 3 pictures: company-coq, refman, Alectryon.

.. note::

   Early on it was Company-Coq; then it was Coq's reference manual.  And then it was Alectryon, the subject of this talk.

   Why am I telling you about these old tools, then? Well, you see, the common thread here is that all these tools started from a place of having an itch to scratch — a need to fulfill — and then sharing the result.  It turns out that in most cases, if you have an itch, many many other people have that same each.  What this means is that there are very few itches that are not worth your time to scratch.

   Which is great, because boy are there itches to scratch in the world of proof assistants! You see, if your language has very limited tools, then the only people who use it are those who don't need or care about advanced tools — just the people that are good enough to survive with limited tools.  And guess what: people who don't need tools don't *write* tools.  Rinse, repeat, and you get to where we are now.

---

TODO XKCD

.. note::

   There's this popular XKCD comic from right around the time I started my PhD.  Here's what it says: (explain the comic).

   This is all well and good if you're working in a vacuum, but there's something misleading about this comic: it says "you" everywhere, so all the calculation assume that you're pitching your time against your time.

   But if you're writing tools that you share with other people, then all this work gets leveraged.  You get to apply a multiplier of tens, hundreds, thousands, or even millions to this "how often you do the task row".

   And if it gets you invited to give a keynote at some point down the line and reminisce about MP3 players, what's not to love?
   Writing tools is just *that cool*.

---

TODO proof presentation paper

.. note::

   Alright, so, what itch are we scratching today?  In one word, “proof presentation” — specifically, the presentation of proof scripts in an interactive theorem prover, like Coq.

   Proof presentation is everything that has to do with displaying a proof, explaining it to another human being, and sharing it with readers.

---

TODO outline

.. note::

   Here's the plan for today.  First, I'm going to tell you more about the specific problem that we're trying to solve, and how Alectryon solves this problem.  Then I'll show you how it works concretely, and finally I'll spend some time outlining an interesting research problem that I'd like to be the next step in this journey.

---

TODO Proof from wiki

.. note::

   Traditionally, a math proof looks roughly like this.  Here we are proving that in a semigroup with a left identity, left inverses are also right inverses.

   This style of proof is called "calculational": the proof is basically a sequence of equalities, with explanations next to each of them.

---

TODO Isabelle proof

.. note::

   The following Isabelle proof does a decent job of capturing this structure.  It's not exactly the same steps, but the interleaving is the same.

---

TODO Coq proof from job talk

.. note::

   Now contrast this with the same proof, in Coq.  There is what we want to prove at the top, Qed at the bottom, and some unintelligible gibberish in the middle.

---

TODO math proof

.. note::

   These days it seems that some folks in the math community are warming up to interactive theorem proving, but this used to be a topic of contention.

---

TODO quotes from Perlis paper on proofs

.. note::

   People use to fight about this!  Who cared if proofs were right, as long as something was learnt from them! (Read the quotes)

   There's something valid to this argument: there is something joyful and fascinating about understanding things deeply that is wholly disconnected from knowing whether a paper proof covers all the minute details and corner cases correctly.

---

TODO theorem from Koika

.. note::

   Of course, not do be overdone, some of us swing all the way to the other side.  The theorem above states correctness for a compiler I wrote not so long ago.  If you're going to use the compiler, does it matter how the 5000 lines Coq proof works?  Its so automated that there are places where even I don't know exactly how it works.  Heck, the best part of my job is when I change the compiler and the proof automation is good enough that it keeps going through.  It tells me the one thing that I care about, which is that the compiler is actually correct.

---

TODO CoqIDE gif

.. note::

   Of course not all proofs are like that: often we are looking to communicate something through the proof.  We are not just proving things to make sure that we're correct; we're also hoping to share the proof.  In Coq the way we can do this is by running inside of a proof assistant.

   TODO: copy text about this not working for offline, etc.

---

TODO import slides on state of the art.

---

TODO import slides on literate programming

---

TODO JSON diff showing before / after Nat redefinition

.. note::

   I won't dive deep into the way Alectryon is implemented, but I'll point out one thing: it's smart enough to decouple your prose from your code, and to cache the results of running the code.  The result is that you get a stable archive of the whole proof, not just the scripts, and you can use that to check for breakage over time.

---

TODO: Demo on how it works

- Basics: Coq document
- IDE support
- Mini-language for customized display
- References and Quotes
- Custom driver
- Extensions for custom rendering
- Polyglot documents
- Diffs on JSON



Check README for things I'd have forgotten.

Taking stock
============

.. note::

   Backing up a bit, let me try to address what's missing.  First I'd like to broaden our perspective on documentation a bit, and second I'd like to talk about a recent development, along with a challenge.

---

What's documentation, anyway?
-----------------------------

Internal, external, and per-object.

.. note::

   I'd argue that given a Coq development, there are really three kinds of documentation that we may want: internal, external, and per-object.

---

TODO alectryon document picture

.. note::

   The first one is “internal documentation”.  It's what Alectryon was originally developed for: interleaving commentary and code in a way that still lets the reader process everything sequentially.  It's exhaustive: the intent is that it serves as a prose description of what's happening throughout a document.  This is the kind of document that you use when you want your reader to be able to reproduce the same tricks.

   TODO: Example of Koika tutorial

---

TODO Hydra-battles

.. note::

   The second one is “external documentation”.  Here the idea is that you have a Coq development that accompanies a mathematical text, but the two live separately.  Still, you want them to be closely connected, so you import definitions, proof fragments, etc. from the Coq code into the math document.  This is the kind of doc you use when you want the reader to have a high-level understanding, coupled with specific places where you zoom in.

   Originally Alectryon didn't support this at all, but recently I've had the pleasure of working with Pierre, Karl, and Théo on extending it.

   The way we did this is by adding markers into the Coq code to make it clear which bits we wanted to import, and using a custom Alectryon driver; but in the long run I'd like to improve Alectryon's quoting and cross-referencing facilities to make this even easier.

---

TODO tactic docs from refman

.. note::

   The third one is per-object documentation: this is the programmer's view of the system.  This is not intended to tell a story or pull multiple objects together; instead, it's an exploded view that documents each object one at a time.

   We don't have a story about this in Alectryon at the moment, short of documenting objects separately from their definitions.  This is what we do in the reference manual of Coq, in fact: we document each object using reStructuredText constructs.

   In the long run I'd like to see better integration of docstrings and per-object documentation into Alectryon.  The idea would be that just like the external docs allow you to pull proof fragments and definitions from a file, they should allow you to pull complete objects, including their docstrings, to allow you to weave a story around these objects, like documenting an API.

   I'm looking for collaborators to work on these aspects, and I hope that you'll join me to build the next generation of self-documenting Coq proofs.

---

On rendering proof objects
--------------------------

.. note::

   The second aspect that I'd like to spend a bit more time on is rendering.  I've given a few demos already, but let me walk through a different example.

---

TODO: Sep logic formula

.. note::

   Here is a separation logic formula.  It captures the way some objects are laid out in memory.
   (Describe the formula)

---

TODO: Sep logic picture

.. note::

   Here is the same formula, rendered in a way that I hope we can all agree is more pleasant.

---

TODO: Step through sep logic proof from Arthur.
TODO: Demo how this works:

- Coq notation to print easily parsable notation
- PEG grammar to parse sep logic
- JS library to cluster the graph and translate it to DOT
- Graphviz library compiled to JavaScript to generate the rendering

---

It's a hack!
------------

.. note::

   This is all nice and well, but it's a hack!  It works for this small example because of the specific way I've designed it, and the same is true for most of these rendering examples that I've shown you.  Think of using LaTeX to render math, for example: it doesn't scale to large Coq terms, and it requires hacking Coq notations.

---

Doing it right
--------------

- Allow alternative notation domains
- Define a rendering language

.. note::

   What's the non-hacky way to do this?

   It's "easy": first we need to allow users to define their own notations.  Basically, we want to extend Coq's notation system to support alternative notation domains: you'd define how to map your Coq code not just to text, but to pictures, latex, etc.

   Notations in these alternative domains would be expressed in domain-specific languages: one for graphs, one for LaTeX math, one for pretty-printed text, one for syntax highlighting, etc.

   The lean folks already do some of this, btw: there's really cool work on widgets that lets you map arbitrary lean structures to HTML.
   I think the problem is that it puts too much responsibility on the programmer.  This will become clear when I walk through the challenges.

---

Challenges
----------

- It requires continuous solutions
- It's optimization problem across multiple domains
- It needs to work well statically but also to allow editing

.. note::

   There are many challenges that make this problem a bit different from traditional DSLs for drawing pictures.

   - First, it requires continuous solutions: small changes in goal ⇒ small changes in picture.  This rules out naive randomized "best placement" algorithms.

     And we want it to work even with partial proofs, so we can't optimize by looking at all proof states.

   - Second, things get really hairy when you get into multiple domains: LaTeX in nodes of graph, or Coq code within deduction rule syntax, etc.  (Describe issue with Coq code inside graph)

   - Third, we're hoping that this works for static media like paper, and even if we can assume interactive media we want users to not have to click through too much.  So, we need a lot of customizability.

     And we need to figure out editing.  My current thinking on this is that we can cheat a bit.  It turns out that in most cases the hierarchical structure of the text is reflected in the figure, and each part of the figure maps to a piece of text, recursively; so, we can just revert to text for the part of the figure that's being edited.

---

Thanks!
=======

TODO: related work

.. note::

   And that's what I'll leave you with!  I've shown some of the related work on this side, because everything that I've presented here exists thanks to half a century of efforts and reflection.  Please come talk to me if you're curious about these issues, and let's use the remaining time we have to discuss what I've missed!

=====================
 A tour of Alectryon
=====================

.. note::

   Back in undergrad I taught in high school for a few months. There was a proof I liked to show my students, because it surprised most of them.

----

.. raw:: html

   <script type="text/javascript">
     MathJax = {
         options: {
             skipHtmlTags: [
                 'script', 'noscript', 'style', 'textarea',
                 'annotation', 'annotation-xml'
             ]
         },
         startup: {
             pageReady: function () {
                 mathjax_setup();
                 return MathJax.startup.defaultPageReady();
             }
         }
     };
   </script>

   <script type="text/javascript" id="MathJax-script" async
      src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js">
   </script>

.. container:: xxxxl

   .. math:: \frac{a}{c} + \frac{b}{d} \not= \frac{a + b}{c + d}

.. note::

   This was the setup: every student knows that you can't sum fractions element-wise.
   What many students don't know is that you *can*, actually, as long as long you're just trying to prove an inequality.

----

.. container:: xxxxl

   .. math:: \frac{a}{c} + \frac{b}{d} \ge \frac{a + b}{c + d}

.. note::

   My main line of research is doing proofs with the Coq proof assistant, so let me share a Coq proof of this inequality.

----

.. raw:: html

   <div style="display: none">
       \(\newcommand{\ccQ}{\mathbb{Q}}\)
       \(\newcommand{\ccNat}{\mathbb{N}}\)
       \(\newcommand{\ccSucc}[1]{\mathrm{S}\:#1}\)
       \(\newcommand{\ccFrac}[2]{\frac{#1}{#2}}\)
       \(\newcommand{\ccPow}[2]{{#1}^{#2}}\)
       \(\newcommand{\ccNot}[1]{{\lnot #1}}\)
       \(\newcommand{\ccEvar}[1]{\textit{\texttt{#1}}}\)
       \(\newcommand{\ccForall}[2]{\forall \: #1. \; #2}\)
       \(\newcommand{\ccNsum}[3]{\sum_{#1 = 0}^{#2} #3}\)
   </div>

.. container:: proof-overlay

   .. code:: coq

      Lemma Qle_pairwise : ∀ a b c d, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
        (a + c)/(b + d) ≤ a/b + c/d.
      Proof with Qeauto.
        intros a b c d H.
        field_simplify...
        rewrite <- (Qmult_le_l (b + d)), Qmult_div_r, Qmult_Qdiv_fact...
        rewrite <- (Qmult_le_l (b * d)), Qmult_div_r...
        field_simplify.
        rewrite <- (Qminus_le_l (b * d * a)); ring_simplify.
        rewrite <- (Qminus_le_l (b * d * c)); ring_simplify.
        Qeauto using Qsqr_0.
      Qed.

   .. class:: substep

      .. image:: coq.png
         :class: rooster-sticker

.. note::

   Statement at top, Qed at bottom, all good?

   How about with a little rooster to the side, convinced now?

   Show of hands: who learnt something deep from looking at this "proof"?

   Proof *script*.  Sequence of steps/tactics like multiply both sides, from premises to conclusion.

   Not what mathematicians call “a proof”.
   Missing *goals*, …. That's because computed.

----

.. image:: coqide.png
   :alt: CoqIDE showing a proof script and a goal.
   :class: img-m

.. note::

   Of course states redundant, in a sense.  But downside: reading a proof script is impossible.


   Sometimes don't why proof is true.  E.g. program properties, or large enumeration of cases.  Coq happy I'm happy.

   But sometimes there's content.  Interesting info.
   Want to show not just steps, goals.

   If readers have Coq installed, OK.
   But sometimes not right version, or proof has dependencies, or compilation slow, or mobile phone, or browsing casually, or… writing book!

   So what do people do to write manuals, tutorials, textbooks, blog posts, or any other piece of text that mixes Coq proofs and prose?

----

.. code:: coq

   Lemma Qle_pairwise : ∀ a b c d, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
     (a + c)/(b + d) ≤ a/b + c/d.
   Proof with Qeauto.
     intros a b c d H.
     (** [(a + c) / (b + d) ≤ a / b + c / d] *)
     field_simplify...
     (** [(a + c) / (b + d) ≤ (a * d + c * b) / (b * d)] *)
     rewrite <- (Qmult_le_l (b + d)), Qmult_div_r, Qmult_Qdiv_fact...
     rewrite <- (Qmult_le_l (b * d)), Qmult_div_r...
     (** [b * d * (a + c) ≤ (b + d) * (a * d + c * b)] *)
     field_simplify.
     (** [b * d * a + b * d * c ≤ b ^ 2 * c + b * d * a + b * d * c + d ^ 2 * a] *)
     rewrite <- (Qminus_le_l (b * d * a)); ring_simplify.
     rewrite <- (Qminus_le_l (b * d * c)); ring_simplify.
     (** [0 ≤ b ^ 2 * c + d ^ 2 * a] *)
     Qeauto using Qsqr_0.
   Qed.

.. note::

   In most cases they do something like this: they run the proof in Coq and then, by hand, they copy the output of each tactic into source code comments.

----

.. code:: coq

   Require Import Arith.
   Print fact.
   (** [[
   fact =
   fix fact (n : nat) : nat :=
     match n with
     | 0 => 1
     | S n0 => S n0 * fact n0
     end
        : nat -> nat
   ]]
   *)

(CPDT)

.. note::

   Here's what it looks like in Certified Programming with Dependent Types.

----

.. code:: coq

   pose D x := if x is 2 then False else True.

   (**
   [[
     H : 2 === 1
     D := fun x : nat =>
          match x with
          | 0 => True
          | 1 => True
          | 2 => False
          | S (S (S _)) => True
          end : nat -> Prop
     ============================
      False
   ]] **)

(Programs and Proofs)

.. note::

   Here's what it looks like in Illya's Programs and Proofs.

----

.. code:: coq

   Print Assumptions function_equality_ex2.
   (* ===>
        Axioms:
        functional_extensionality :
            forall (X Y : Type) (f g : X -> Y),
                   (forall x : X, f x = g x) -> f = g *)

(Software foundations)

.. note::

   Here's what it looks like in Software Foundations.

   Super cumbersome.  Lots of work, lots of mistakes.
   Copy pasted output gets out of sync — we all know even high level comments get out of sync fast.

   Wait for readers to find the issues.

   There's got to be a better way, and that's where Alectryon comes in.

   Alectryon two things:

   1. Compiler: captures Coq output and interleaves it in original proof script as webpage.
   2. Literate programming system for Coq.


----

.. container:: alectryon-block

   .. coq:: unfold no-hyps

      Require Import Qle. (* .none *)
      Module Ex1. (* .none *)
      Lemma Qle_pairwise : ∀ a b c d, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
        (a + c)/(b + d) ≤ a/b + c/d. (* .fold *)
      Proof with Qeauto. (* .fold *)
        intros a b c d H.
        field_simplify...
        rewrite <- (Qmult_le_l (b + d)), Qmult_div_r, Qmult_Qdiv_fact... (* .fold *)
        rewrite <- (Qmult_le_l (b * d)), Qmult_div_r...
        field_simplify.
        rewrite <- (Qminus_le_l (b * d * a)); ring_simplify. (* .fold *)
        rewrite <- (Qminus_le_l (b * d * c)); ring_simplify.
        Qeauto using Qsqr_0.
      Qed.
      End Ex1. (* .none *)

.. note::

   Here's the same proof.  Took file, fed Coq, collected output, formatted, and generated interactive visualization.

   Interactive webpage; every proof step is button that reveals proof state.

   After every change can rerun Alectryon and regen the page.

   Outputs recorded, all static: no need to load Coq.

   Everything is web technologies → flexible rendering.

----

.. container:: coq-mathjax

   .. coq:: unfold no-hyps

      Module Ex3. (* .none *)
      Import LatexNotations. (* .none *)
      Lemma Qle_pairwise : ∀ a b c d, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
        (a + c)/(b + d) ≤ a/b + c/d. (* .fold *)
      Proof with Qeauto. (* .fold *)
        intros a b c d H.
        field_simplify...
        rewrite <- (Qmult_le_l (b + d)), Qmult_div_r, Qmult_Qdiv_fact... (* .fold *)
        rewrite <- (Qmult_le_l (b * d)), Qmult_div_r...
        field_simplify.
        rewrite <- (Qminus_le_l (b * d * a)); ring_simplify. (* .fold *)
        rewrite <- (Qminus_le_l (b * d * c)); ring_simplify.
        Qeauto using Qsqr_0.
      Qed.
      End Ex3. (* .none *)
      Open Scope nat_scope. (* .none *)

.. note::

   Use web tech to give meaningful rendering.
   Good shot at understanding: sum fracs, same denominator, cancel, greater than 0

..
   ----

   .. coq:: unfold

      Lemma Gauss: ∀ n, 2 * (sum n) = n * (n + 1). (* .fold *)
      Proof. (* .fold *)
        induction n. (* .fold *)
        - (* n ← 0 *)
          reflexivity.
        - (* n ← S _ *)
          cbn [sum].
          rewrite Mult.mult_plus_distr_l.
          rewrite IHn.
          ring_simplify.
          reflexivity.
      Qed.

   .. note::

      Here's what it looks on another simple proof, forgetting about the fancy LaTeX stuff for a moment.

----

.. coq::

   Section classical. (* .none *)
     Context (excl: ∀ A, A ∨ ~ A).
     Goal ∀ A, ¬¬A → A.
       intros A notnot_A. (* .in *)
       Show Proof. (* .messages .unfold *)
       destruct (excl A) as [a | na]. (* .in *)
       Show Proof. (* .messages .unfold *)
       - assumption. (* .in *)
         Show Proof. (* .messages .unfold *)
     Abort. (* .none *)
   End classical. (* .none *)

.. note::

   Here's different example of using Alectryon to help readers develop better understanding.

   And that's what first part of Alectryon is about!  Alectryon automatically annotates proof scripts with Coq's output, generating a complete record of the proof that captures the intermediate proof states and renders them.

----

.. coq::

   (** So far, it looks like co-inductive types might be a magic
       bullet, allowing us to import all of the
       Haskeller's usual tricks. …

       The restriction for co-inductive types shows up as
       the%\index{guardedness condition}% _guardedness
       condition_.  First, consider this stream definition,
       which would be legal in Haskell.

       [[
       CoFixpoint looper : stream nat := looper.
       ]]

       <<
       Error:
       Recursive definition of looper is ill-formed.
       In environment
       looper : stream nat
       unguarded recursive call in "looper"
       >> **)

.. note::

   OK, so this solves 1 problem: displaying goals and outputs.
   But there's another aspect of writing about Coq proofs: the explanatory prose.

   There's no code here: it's all prose, embedded in source code comments.

   Lots of respect.  Whole other level of determination and grit to edit whole book in comments.

----

.. code:: coq

   (*|
   A fairly common occurrence when working with dependent
   types in Coq is to call `Compute` on a benign expression
   and get back a giant, partially-reduced term, like this:
   |*)

   Import EqNotations Vector.VectorNotations.
   Compute (hd (rew (Nat.add_1_r 3)
                    in ([1; 2; 3] ++ [4]))). (* .unfold *)

   (*|
   This post shows how to work around this issue.
   |*)

.. note::

   Shouldn't have to be this way; I want to use a text editor for text, and a code editor for code.

   Alectryon solves this by allowing you to toggle between views of your code.

   First looks very similar; but then I can switch to “prose mode”.
   Uses reStructuredText, very popular.
   Switch back.

   In prose mode get completion of english words, spellchecking, live preview.
   In code mode get Proof General experience, ITP.

----

.. code:: rst

   A fairly common occurrence when working with dependent
   types in Coq is to call `Compute` on a benign expression
   and get back a giant, partially-reduced term, like this:

   .. coq::

      Import EqNotations Vector.VectorNotations.
      Compute (hd (rew (Nat.add_1_r 3)
                       in ([1; 2; 3] ++ [4]))). (* .unfold *)

   This post shows how to work around this issue.

.. note::

   This is what it looks like after flipping the code and the prose around.  The syntax is reStructuredText.  reStructuredText is a great markup language, very much like Markdown but with a robust story for writing extensions; in fact, I used this whole presentation is just one large Coq file; I used Alectryon to convert it to reStructuredText.

   The best part is that you can go back: once you're done editing the prose of your document and you're ready to resume hacking on the proofs, you can use Alectryon to convert the reStructuredText file back into a Coq source file, in which the prose is wrapped in special comments and the code is at the top level.  Here, let's go back to the original code.

----

.. image:: emacs-screenshot.svg
   :alt: A screenshot of Emacs shows the same snippet from Software foundations, in code and prose views.


.. note::

   These two transformations are the inverse of one another, so you can switch between the code-oriented view and the prose-oriented view at will.  This is trivial to integrate into an IDE; I did it for Emacs, and I'm sure it would be very easy to do in any other editor.

   Being able to go back and forth between reStructuredText and Coq means that Alectryon does not have to implement its own markup language for literate comments: it can just piggyback on the existing reStructuredText toolchain, which is very robust and used by a lot of people for all sorts of documents, like the reference manuals of Python, Agda, Haskell, and a host of other languages — including Coq.

----

.. role:: red
   :class: red

.. role:: green
   :class: green

.. container:: xxxl

   :red:`✗` LaTeX ← literate document → Coq

   :green:`✓` reST ⇆ Coq

.. note::

   If you know literate, you might be confused.
   Normally tangling and weaving.
   There's a main document that you edit, then two views that you generate.
   Can't edit those.

   Not too bad except tooling for regular languages.

   Unusable for Coq: need interactive UI.  Hence all proof-heavy books written as Coq files.

   Alectryon is different: no main document, just tangled and weaved, and bidirectional conversion.  Chose which one to work with as needed.

----

================
 Implementation
================

.. container:: s

   Generate an interactive webpage from a literate Coq file with reST comments (Coqdoc style):
      .. code::

         ../alectryon.py literate.v

   Generate an interactive webpage from a plain Coq file (Proof General style):
      .. code::

         ../alectryon.py --frontend coq plain.v

   Generate an interactive webpage from a Coqdoc file (compatibility mode):
      .. code::

         ../alectryon.py --frontend coqdoc literate.v

   Compile a reStructuredText document containing ``.. coq::`` blocks (coqrst style):
      .. code::

         ../alectryon.py literate.v.rst

   Translate a reStructuredText document into a literate Coq file:
      .. code::

         ../alectryon.py literate.v.rst -o literate.v

   Translate a literate Coq file into a reStructuredText document:
      .. code::

         ../alectryon.py literate.v -o literate.v.rst

   Record goals and responses for fragments contained in a JSON source file:
      .. code::

         ../alectryon.py fragments.json

   Record goals and responses and format them as HTML for fragments contained in a JSON source file:
      .. code::

         ../alectryon.py fragments.json -o fragments.snippets.html

.. note::

   Now that I've given you a sense of what Alectryon does, let me say a bit about how it does it.

   Alectryon is a Python program, and it's written as a collection of mostly independent modules:

----

.. coq:: unfold

   (* Can you favorite IDE handle this?
      (mine can't, and I'm one of the maintainers…) *)
   Notation "( a . b )" := (a, b).
   Check (0 . 1).

.. note::

   Coq frontend.

----

.. container:: coq-mathjax

   .. coq:: unfold

      Module Gauss. (* .none *)
      Import LatexNotations. (* .none *)
      Lemma Gauss: ∀ n, 2 * (nsum n (fun i => i)) = n * (n + 1).
      Proof. (* .fold *)
        induction n; cbn [nsum]. (* .fold *)
        - (* n ← 0 *)
          reflexivity.
        - (* n ← S _ *)
          rewrite Mult.mult_plus_distr_l. (* .no-hyps *)
          rewrite IHn. (* .no-hyps *)
          ring.
      Qed.
      End Gauss. (* .none *)

.. note::

   Transforms to post-process Coq's output; either in Python or later in JS.

----

.. raw:: html

   <script src="https://d3js.org/d3.v5.min.js" charset="utf-8"></script>
   <script src="https://dagrejs.github.io/project/dagre-d3/latest/dagre-d3.js"></script>

.. container:: rbt-no-printing

   .. coq::

      Require Import RBT. (* .none *)
      Module RBT1. (* .none *)
      Definition build_trees (leaves: list nat) :=
        List.fold_left (fun trs n => RBT.add n (hd RBT.empty trs) :: trs)
          leaves [] |> List.rev.

      Compute build_trees [1;2;3;4;5]. (* .unfold *)
      Compute build_trees [2;1;4;3;6].
      End RBT1. (* .none *)

.. note::

   Concrete example: understand red-black trees.

----

.. container:: rbt-render

   .. coq::

      Module RBT2. (* .none *)
      Import RBTNotations. (* .none *)
      Definition build_trees (leaves: list nat) :=
        List.fold_left (fun trs n => RBT.add n (hd RBT.empty trs) :: trs)
          leaves [] |> List.rev.

      Compute build_trees [1;2;3;4;5]. (* .unfold *)
      Compute build_trees [2;1;4;3;6]. (* .unfold *)
      End RBT2. (* .none *)

.. note::

   Now with graphs!

----

.. image:: udiv.opt.paths.svg
   :alt: A piece of Coq code showing a binary object rendered by passing it to objdump and highlighting the result.

.. note::

   Second example: objdump.

----

.. image:: rss.paths.svg
   :class: img-m

.. note::

   Another component: HTML export.  Careful to use the right web tech to support wide range of use cases, including RSS feeds.

----

.. code:: coq

   Check "Where does this string (|* end? ".
   (*| And where does `"this comment *|)` end?" |*)
   Check "here? *)".

.. code:: rst

   .. coq::

      Check "Where does this string (|* end? ".

   And where does `"this comment *|)` end?"

   .. coq::

      Check "here? *)".

.. note::

   Then literate module to weave and tangle back and forth.
   Must keep track of positions, so keep context when switching views.

----

.. image:: sphinx.png
   :class: img-m

.. note::

   Finally connect to reStructuredText or Markdown pipelines with Docutils and Sphinx.

----

============
 Evaluation
============

.. note::

   The paper has a lot of evaluation, and I encourage you to check it out if you're curious; in brief, the evaluation is organized around two axes:

----

.. image:: polymorphic-universes-8-12.svg
   :class: img-m

.. note::

   First axis: robustness.  Compiled hundreds of thousands of lines of Coq code, all of standard library, books, tutorials: it works.  Even compiled entire first volume of Software foundations.

   Confusing!  I said reST but SF is coqdoc.  Actually example of extensibility.  Using coqdoc as markup language for prose, and code with Alectryon.

----

.. container:: twocolumns

   .. image:: stdlib.paths.svg
      :class: img-stdlib

   .. image:: breakdowns.paths.svg
      :class: img-breakdowns

.. note::

   The second axis measures Alectryon's speed.  All the graphs are in the paper, but the long story short is that Alectryon has a median overhead of 3x on compilation times (90% of all files fall below 7x), and a good 1/3 of that is communication overhead that can probably be eliminated in the future.  The rest is the overhead of collecting and formatting goals, which can be pretty costly for files that have a many goals.

----

==============
 Related work
==============

.. image:: citations.paths.svg

.. note::

   It's hard to do justice to all the related work in this area in just a few minutes, so I'll simply say that Alectryon builds on decades of great ideas for making programs and proofs more understandable, all the way from a paper in 1980 co-authored by Eric Schmidt and Phil Wadler to PhD theses written just a year ago.  There's 60 citations and three pages of related work in the paper; if you're curious about the history of this stuff, you should really have a look.

----

.. container:: xxxl

   | `<https://github.com/cpitclaudel/alectryon/>`__
   | `<https://alectryon-paper.github.io/>`__

.. note::

   To recap, Alectryon provides an architecture to record and visualize Coq proofs, facilitating sharing and interactive exploration of proof scripts; and a bidirectional translator between woven and tangled documents, enabling seamless editing of prose and code.

   Alectryon is freely available on GitHub, and it's received great reception from the community.

----

.. container:: xxxxl

   .. math:: \LaTeX

.. note::

   Maybe I can conclude with a few words about the next steps.  Here are some directions that I'm exploring or would like help exploring.
   First, I'd like to make a LaTeX backend: reStructuredText can produce LaTeX in addition to HTML, so it would make sense to support that as well.  I have a branch for this, and it's almost ready.

----

.. image:: life.svg

.. note::

   Second, I'd like to explore advanced visualizations further.  There are many domains for which the natural visualization for a piece of data is not text.  I have a few examples in the paper, but I'd like to push that idea further.  In fact, what would be really neat would be to settle on a standard for Coq developments to specify how to render a particular type.  I'm thinking of display-only notations that would produce images, graphs, plots, etc.  Once we have this, we could even integrate it with IDEs and finally stop envying the Racket folks with their magic picture tricks.

----

.. coq:: none

   Require Import String.
   Inductive Prog :=
   | Boring0
   | Boring1
   | Bind (var: string) (expr: Prog) (body: Prog)
   | Boring2
   | Boring3.

   Inductive Value: Type :=
     BoringValue.

   Inductive ComputesTo : Prog -> Value -> Prop :=
   | ComputesToAny : forall p v, ComputesTo p v.

   Definition context := list (string * Value).

   Require Import Lists.List.
   Import ListNotations.

   Fixpoint interp (gamma: context) (p: Prog) :=
     match p with
     | Bind var expr body => let val := interp gamma expr in interp ((var, val) :: gamma) body
     | _ => BoringValue
     end.

   Tactic Notation "t" := constructor.
   Tactic Notation "…" := constructor.

.. coq::

   Lemma interp_sound: forall (p: Prog) (gamma: context) (v: Value),
       ComputesTo p (interp gamma p).
   Proof.
     induction p; intros.
     - t.
     - t.
     - simpl. (* .unfold *)
       ….
     - t.
     - t.
   Qed.

.. note::

   Third, for all the machine learning wizards out there, I'd like to explore automatic proof summarization — just like automatically identifying the most exciting moments of a soccer game, but for Coq proofs.  More formally, the task is to automatically identify a small subset of proof steps that lead to particularly interesting or relevant goals; we'd use this in combination with Alectryon to identify the most interesting parts of a proof development.

----

.. image:: provers.svg

.. note::

   Finally, I'd like to extend the system to other languages, both for the markup side and for the Coq side.  I built Alectryon with Coq and reStructuredText, but very little of it is actually Coq or reStructuredText specific.

   To port Alectryon to a different language, like Lean for example, you would need to add a Python module that invokes Lean and collects its output, and if you also wanted the literate programming support you'd want to make a bidirectional translator for Lean's comment syntax.

   The literate programming parts were actually inspired by work that I did for F* a few years ago, so adding new languages really shouldn't be too hard.  If you're interested in getting Alectryon to work with your favorite proof assistant, please get in touch.

----

.. container:: xxxl

   | `<https://github.com/cpitclaudel/alectryon/>`__
   | `<https://alectryon-paper.github.io/>`__

.. note::

   Thanks for your attention!  Feel free to reach out if you have questions, and check the README and the paper for lots of extra info.
