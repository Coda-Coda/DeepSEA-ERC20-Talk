Hi all,

I've just released [Alectryon 1.0](https://github.com/cpitclaudel/alectryon)! Alectryon is a collection of tools for writing technical documents that mix Coq code and prose. It includes a compiler that produces interactive webpages from Coq source files, as well as tools to translate back and forth between Coq and reStructuredText, allowing you to toggle between the *proof* and *prose* views of a file at will as you edit it.  From [the blog post](https://plv.csail.mit.edu/blog/alectryon.html):

> Coq proofs are hard to understand in isolation: unlike pen-and-paper proofs, proof scripts only record the steps to take (induct on _x_, apply a theorem, …), not the _states_ (_goals_) that these steps lead to.  As a result, plain proof scripts are essentially incomprehensible without the assistance of an interactive interface like CoqIDE or Proof General.

> Alectryon was written with two scenarios in mind:
>
> -   Making it easier to browse Coq developments (even if these developments are not written in literate style) by turning Coq source files into webpages allowing readers to replay proofs in their browser (the “Proviola” style). As a demo, I recorded goals and responses for [a](https://alectryon-paper.github.io/bench/flocq-3.3.1/src/Core/Digits.html) [complete](https://alectryon-paper.github.io/bench/flocq-3.3.1/src/Core/Round_NE.html) [build](https://alectryon-paper.github.io/bench/flocq-3.3.1/src/Prop/Sterbenz.html) of the [Flocq library](https://alectryon-paper.github.io/bench/flocq-3.3.1/src/).
>
> -   Writing documents mixing Coq source code and explanatory prose, either starting from a text file containing special directives (the “coqtex” and “coqrst” style, used in Coq's reference manual), or starting from a Coq file containing special comments (the “coqdoc” style, used in CPDT, Software foundations, etc.).
>
>     The Alectryon paper, this blog post, and my SLE talk are examples of the former (they are written in reStructuredText, a Markdown-like markup language); as another example, here is [a chapter from FRAP](https://alectryon-paper.github.io/bench/books/interpreters.html) and [one from CPDT](https://alectryon-paper.github.io/bench/books/proof-by-reflection.html), converted to reStructuredText by hand (change the URLs to `.rst` to see the sources).
>
>     As a demo of the latter here's [a full build of Logical Foundations](https://alectryon-paper.github.io/bench/lf/).

Read on on [the PLV blog](https://plv.csail.mit.edu/blog/alectryon.html) for more explanations, demos, and a tutorial, check out [the repository](https://github.com/cpitclaudel/alectryon) to get started using Alectryon, or read the [academic paper](https://pit-claudel.fr/clement/papers/alectryon-SLE20.pdf) (open access) for lots more details and plenty of nifty pictures.

Oh, and I have a talk about this [at SLE2020](https://conf.researchr.org/details/sle-2020/sle-2020-papers/11/Untangling-mechanized-proofs) on Monday; you should join!

Happy tangling!
Clément.


Just released! Alectryon 1.0 is a compiler from Coq documents to interactive webpages + a literate programming toolkit. I'm hoping to make it easier to write textbooks, blog posts, and other documents that mix Coq code and prose.  Blog post at https://plv.csail.mit.edu/blog/alectryon.html, repo at https://github.com/cpitclaudel/alectryon, and open-access paper at https://pit-claudel.fr/clement/papers/alectryon-SLE20.pdf — come to the SLE talk on tomorrow!
