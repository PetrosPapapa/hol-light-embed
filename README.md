# Object level reasoning with embedded logics in HOL Light
## Petros Papapanagiotou (pe.p@ed.ac.uk) and Jacques Fleuriot (jdf@inf.ed.ac.uk)
[Centre of Intelligent Systems and their Applications](http://web.inf.ed.ac.uk/cisa)
[School of Informatics, University of Edinburgh](https://www.ed.ac.uk/informatics/)


## About

This is a generic framework to perform object level reasoning with embedded logics in [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light/).

It provides procedural tactics inspired by [Isabelle](https://isabelle.in.tum.de/)'s rule/erule/drule/frule.

It also supports correspondences with computational terms in the style of Curry-Howard.

Further information and background will be provided in a forthcoming publication.

### What this library does

Assuming you have an inductively defined logic embedded in HOL, the library allows you to prove object level theorems within your embedded logic. All the boilerplate around rule matching and meta-level term management is taken care of automatically without any additional coding.

Assuming an embedding of a constructive correspondence of a logic to some computational calculus (in the style of Curry-Howard) the library additionally automates the construction of the terms as the proof progresses. This is accomplished through the use of metavariables and delayed instantiation. 

In effect, this allows the construction of any program via proof using any logic correspondence that can be embedded in HOL Light in the ways described below.

It is worth noting that the tactics can be used programmatically as well, e.g. towards automated proof tools for the embedded logic.


### What this library does NOT do

It does **not** allow you to perform any meta-level reasoning (such as cut-elimination proofs). It deals with shallow embeddings where the derivation semantics of the logic are mapped to HOL implication. At this level it is not possible to reason about the semantics of the embedded logic.


## Getting started

The framework can run on top of a running HOL Light instance as any library. It does have certain dependencies as described below.

### Requirements

Essential requirements for the software to run:

1. OCaml 4.07.0 minimum. The easiest way to install this is through [opam](http://opam.ocaml.org/).
2. The [HOL Light](https://github.com/jrh13/hol-light) theorem prover. It comes with its own [installation instructions](https://github.com/jrh13/hol-light/blob/master/README).


### HOL Light Dependencies

The framework depends on the following HOL Light libraries:

1. The [Isabelle Light](https://bitbucket.org/petrospapapa/isabelle-light) library. This also comes bundled with HOL Light by default.
2. Additional [HOL Light tools](https://github.com/PetrosPapapa/hol-light-tools). This consists of snippets of code and libraries I have implemented. Although some of these were implemented in parallel to this project, they have a more general function and so are kept separately.


### Fresh install

The fastest way to install is by checking out [this fork of HOL Light](https://github.com/PetrosPapapa/hol-light):

```
git clone https://github.com/PetrosPapapa/hol-light.git

```

The fork contains the required libraries as submodules which can be checked out as follows:

```
git submodule update --init --recursive
```

Note, however, that the fork includes additional submodules from other projects, some of which may be private. This will result in errors when updating the submodules, but does not affect this particular library.

You can then follow the standard [HOL Light installation instructions](https://github.com/jrh13/hol-light/blob/master/README) as you would with the regular HOL Light repository.



### Install to an existing instance of HOL Light

If you already have HOL Light up and running and want to add this library, you will need to clone the 2 required repositories as follows:

```
cd hol-light/
git clone https://github.com/PetrosPapapa/hol-light-tools.git tools
git clone https://github.com/PetrosPapapa/hol-light-embed.git embed
```

### Loading the library

Once HOL Light is up and running and the library is installed, you can load it with the following command:

``` OCaml
loads ("embed/sequent.ml");;
```



## Examples

The usage information below highlights the main available tools and functionality. This is much easier to follow in the context of the examples provided:

* [Examples/Church.ml](https://github.com/PetrosPapapa/hol-light-embed/blob/master/Examples/Church.ml) contains 2 embeddings. The first one is a subset of propositional logic involving only conjunction and implication. The second is a subset of Church's simply-typed lambda-calculus, including only conjunction and implication. Some example interactive proofs are also included. The 2 embeddings can be contrasted to show how the same proofs can work with or without a computational correspondence.
* [Examples/ILL.ml](https://github.com/PetrosPapapa/hol-light-embed/blob/master/Examples/ILL.ml) includes a simple embedding of Intuitionistic Linear Logic and some packaged proofs.
* [Examples/pas/](https://github.com/PetrosPapapa/hol-light-embed/tree/master/Examples/pas) includes an embedding of the Propositions-as-Sessions correspondence described in [this paper by Philip Wadler](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions-jfp.pdf). This is a correspondence between Classical Linear Logic and a session type calculus named CP. The example also includes the implementation of some automated proof procedures for Classical Linear Logic to demonstrate how the tactics can be used programmatically. Example proofs can be found in [Examples/pas/examples.ml](https://github.com/PetrosPapapa/hol-light-embed/blob/master/Examples/pas/examples.ml).



## Using the library

The library can be used to perform object level reasoning with embedded logics. The examples provided above can put much of this information in context.


### Embedded logics

A typical way of embedding a logic in HOL Light is through an inductive definition of its inference rules using `new_inductive_definition`. This involves the definition of a consequence operator (turnstile). Valid derivations are defined inductively using standard (classical) HOL implication. 

Although this is sometimes refered to as a **deep embedding** in the literature, it is really a **shallow** one as we do not formalise the semantics of the logic.

The library currently only supports a **sequent calculus** style, although we have plans for a **natural deduction** setup in the future. It supports one-sided, two-sided, classical, and intuitionistic (single conclusion) sequents.

Although sequent parts can be modelled arbitrarily, the library provides extended support for **multisets of terms**. The following 2 operators can be used to define your multisets:
* `'` is a prefix for a singleton multiset
* `^` is an infix operator for multiset union

Multisets allow high flexibility with the ordering of the terms. However, substructural logics without the `Exchange` rule obviously cannot be modelled in this way.

### Construction

Correspondences generally involve computational terms (e.g. in lambda-calculus) annotated with logic terms (types). The library does not differentiate between terms and their annotations. Construction is only attempted on metavariables (see below).


In some cases (such as in correspondences of Classical Linear Logic) the whole sequent is also annotated with a process term. This can be accomplished by adding an additional argument to the consequence operator (turnstile).


### Types of proofs

The library anticipates 2 types of proofs:

1. **Regular / type-checking** proofs: these involve object level lemmas where all computational annotations (if any) are provided already. In simple logics, this is just a regular object level proof, whereas in constructive logics these are essentially proofs that type check the given computational terms.
2. **Construction** proofs: these involve proofs in logics with a computational correspondence where the annotations are not known in advance. The aim of the proof is to construct a computational term that corresponds to the derived type. 
  This is accomplished by initializing the unknown computational term as a metavariable. The best way to achieve that is to existentially quantify the term and then use `META_EXISTS_TAC`. The rest of the proof can then proceed as any other proof. Once the (interactive) proof is completed, the instantiation of the term can be obtained via `top_inst(p())` (where `p()` is the toplevel HOL Light goal state).
  


### Proof system

In order to automate the meta-level term management and bookkeeping (particularly metavariables) the whole HOL Light proof system is essentially reconstructed. The aim is to allow the extension of the proof state with additional metadata.

This results to the introduction of a `seqtactic` as an extension of the standard HOL Light `tactic`. Associated proof tools are also extended as follows:

* `ETHEN`, `EEVERY`, `ETHENL` etc. extend their counterpart HOL Light tacticals
* `eseq` extends `e`
* `prove_seq` extends `prove`
* `ETAC` (or `SEQTAC`) can lift a `tactic` to become a `seqtactic`
 
### Tactics

The main tactics (of type `seqtactic`) are built in the spirit of [Isabelle Light](https://bitbucket.org/petrospapapa/isabelle-light):

* `ruleseq`: Backward reasoning - match the current goal
* `eruleseq`: Elimination reasoning - match the major assumption and the current goal
* `druleseq`: Destruction reasoning - match and delete the major assumption
* `fruleseq`: Forward reasoning - match and keep the major assumption
* `seqassumption`: Match the current goal to one of the assumption

These extend their Isabelle Light counterparts by taking care of multiset matching and term construction automatically.

Any embedded rule (assuming Isabelle Light's meta-implication operator is used) can be applied using these tactics. Instantiation lists can be used to manipulate the particular application of the rule.


## Additional information

Contact: Petros Papapanagiotou – pe.p@ed.ac.uk - [@PetrosPapapa](https://twitter.com/petrospapapa) 

Distributed under the BSD 3-Clause Revised license. See [LICENSE](https://github.com/PetrosPapapa/hol-light-embed/blob/master/LICENSE) for more information.

<https://github.com/PetrosPapapa/hol-light-embed>
