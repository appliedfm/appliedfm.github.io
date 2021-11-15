---
# layout: post
title:  "Applying categories"
# date:   2021-11-22 6:00:00 -0800
categories: category-theory
---

We look at different ways people are applying category theory in software engineering, computer science, and mathematics.

# Love at first sight

My first introduction to the power of categorical language was [Jack Lee's](https://sites.math.washington.edu/~lee/) books on manifolds. I'm particularly fond of the 2nd book in the series (_Introduction to Smooth Manifolds_) which does a beautiful job showing how all of the parts fit together:

* How to perform _calculations_ in a chosen coordinate frame;
* Construction of the _meta-theory_, including deRham cohomology;
* Showing how _universal properties_ can be used to characterize & encapsulate various constructions.

Through the Curry-Howard lens, we could say that his books develop the _computational_ theory of manifolds (taking multivariable calculus as the "runtime" environment), the _meta-theory_ (up-to and including cohomology), and the _abstract interface_ (expressed via universal properties).

This "architecture" is _extremely_ common in pure mathematics. But why? And what can engineers & computer scientists learn from it? Let's dive in.

# What is a category?

Let's hop into Coq and find out. First we install [John Wiegley's amazing category theory library](https://github.com/jwiegley/category-theory):

```console
tcarstens@pop-os:~$ git clone git@github.com:jwiegley/category-theory.git
tcarstens@pop-os:~$ cd category-theory/
tcarstens@pop-os:~/category-theory$ opam install ./coq-category-theory.opam
```

Now we can see what a category is:

```coq
tcarstens@pop-os:~/category-theory$ coqtop
Welcome to Coq 8.13.2 (October 2021)

Coq < From Category Require Import Theory.
[Loading ML file extraction_plugin.cmxs ... done]
[Loading ML file ring_plugin.cmxs ... done]

Coq < Print Category.
Class Category := {
  obj : Type;

  uhom := Type : Type;
  hom : obj -> obj -> uhom where "a ~> b" := (hom a b);
  homset :> ∀ X Y, Setoid (X ~> Y);

  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);

  compose_respects x y z :>
    Proper (equiv ==> equiv ==> equiv) (@compose x y z);

  dom {x y} (f: x ~> y) := x;
  cod {x y} (f: x ~> y) := y;

  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;

  comp_assoc {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;
  comp_assoc_sym {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
}.
```

This looks intimidating at first (so many parts to understand!) but if you look closely there's only two fields that really matter:

```coq
  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z;
```

Everything else in the `Category` definition is either:

* Stuff that supports the definition of `id` and `compose` (notably the `~>` notation), or
* Equations about `id` and `compose` (such as `id_left` and `comp_assoc`).

So, what is a category? Just as a _ring_ is an abstract generalization of addition and multiplication, a _category_ is an abstract generalization of composition.

This means:
* A category is not "a graph with composition." There's no need to mention any graphs here, and the mental image of a bunch of vertices & edges does not give a good sense of what categories are about. It's _just_ composition.
* `obj` and `hom` are not as important as you might think.
  * Technically speaking, `obj`'s only job is to support the definition of `hom` (`~>`).
  * Similarly, `hom`'s only job is to support the definition of `id` and `compose`.

Why do people associate categories with graphs? Probably because they are accustomed to seeing _commutative diagrams_, a common way of graphically representing one or more equations in a category.

Let's look at an example. The following ASCII art is a _commutative diagram_ that encodes the following situation: _Let `C: Category`, `X, Y, Z, W: obj C`, `f: Y ~> Z`, `g: X ~> Y`, `k: X ~> W`, and `h: W ~> Z` such that `f ∘ g = h ∘ k`._

    X -- k --> W
    |          |
    g          h
    |          |
    v          v
    Y -- f --> Z

The diagram looks like a graph: each node is labeled with a term of type `obj` and each edge is labeled with a term of the appropriate `hom` type.

But a commutative diagram is not _just_ a graph: it is a statement about the _paths_ in the graph. In particular, when we say a diagram "commutes" we mean is that _every pair of parallel paths are equal under composition._ In the diagram above, the paths `f ∘ g` and `h ∘ k` are parallel; since `f ∘ g = h ∘ k`, the we say "the diagram commutes."

Why are commutative diagrams so common in category theory?

Well, given a category and nothing else, the _only_ thing you can do is make statements about which things `compose` to equal which other things. You _could_ do it without drawing any pictures, but most people agree the pictures look cool (when done right).

# Why are categories useful in mathematics?

Now that you know what a category is (an abstract way to talk about equations involving composition) and the main tool of the trade (commutative diagrams), we can talk about why categories are useful in mathematics.

In my view it boils down to three things:

1. _Composition_ is a foundational concept in many mathematical theories. (Often that's because _functions_ are also a foundational concept, but strictly speaking there are many situations where it's possible to have "composition" without having functions.) Because of this, many mathematical theories are natively compatible with categorical language. Algebra, topology, and logic are all great examples.

2. Certain commutative diagrams appear in throught different branches of mathematics. Products, limits, pullbacks, slices, initial objects, and their duals are great examples. For many mathematicians, this fact propels category theory to "lingua franca" status.

3. The converse of (2) is also true: in many mathematical theories, the main constructions can often be characterized by "universal properties." Often these properties take the shape of a familiar commutative diagram, but even when they don't, they still tend to be more succinct than their non-categorical counterparts.

So that's it: categories are useful because they are compatible with many existing theories and because they give us a succinct taxonomy & meta-theory of common structures.


# How do people use category theory in computer science?

From what I've seen, most applications of category theory in CS fall into one of 4, uh, categories. For each category I tried to pick 1 illustrative, contemporary example.

**Interpreting categorical constructions within the context of functional programming**

[Bartosz Milewski](https://bartoszmilewski.com/) (and others) have spent years writing & presenting on the intersection of functional programming & category theory. This topic has a long history in the Haskell community (see this [2009 blog post](http://blog.sigfpe.com/2009/10/what-category-do-haskell-types-and.html) by Dan Piponi). These explorations can be a great way to get a hands-on feel for various constructions in category theory, and in certain domains can also provide clarity when designing new libraries and abstractions. The most famous examples are [monads](https://bartoszmilewski.com/category/monads/), [applicative functors](https://bartoszmilewski.com/2017/02/06/applicative-functors/), [lenses](https://bartoszmilewski.com/category/lens/), and [polynomial functors](https://bartoszmilewski.com/tag/polynomial-functors/).

**A tool for measuring the completeness of a theory**

[Indirection theory](https://dl.acm.org/doi/10.1145/1706299.1706322?cid=81100498630) is a framework for building semantic models of recursive, higher-order, impredicative separation logics. It is a key ingredient in the [Verified Software Toolchain](https://vst.cs.princeton.edu/). In their paper, Hobor, Dockins, and Appel describe indirection theory by stating its key properties, building a model with those properties, then showing that any two models with these properties are isomorphic (in the appropriate sense).

This last part is framework's _universal property_. Regarding the implications of this property, the authors write

> Categorical axiomizations are sufficiently uncommon that we examine the implications. Most importantly, the axioms of indirection theory given in §3 are in some sense complete: they define a particular class of models in a definitive way. Moreover, there seems to be little point in developing alternatives to the construction we presented in §8, at least in CiC.

**A taxonomy & abstraction layer**

[Interaction trees](https://dl.acm.org/doi/10.1145/3371119) are a data structure for representing the behaviors of effectful functions. They are closely related to monads but provide some additional structure that comes in handy when proving stuff about programs. In their seminal paper, Xia et al point out various categorical structures that appear along the way, observing that _KTrees are the morphisms of ... the Kleisli category of the monad `itree E`,_ _event handlers form a cocartesian category,_ _the loop combinator equips KTrees with the well-studied structure of a traced monoidal category,_ etc.

Regarding the utility of these observations, the authors write

> Similarly, the KTree category is just one instance of a Kleisli category, which can be defined for any monad M. Monadic event interpreters, introduced next, build on these structures, letting us (generically) lift the equational theory of KTrees to event interpreters too. This compositionality is important for scaling equational reasoning to situations involving many kinds of events.

In other words, the framework uses categorical ideas as an abstraction layer. This allows the framework to invoke various standard constructions from category theory, which in turn wind up having good properties with respect to equational reasoning and composability.

In some ways this application of category theory looks somewhat similar to the first application area we looked at ("interpreting categorical constructions within the context of functional programming"). Indeed, both talk a lot about monads.

But I'd argue that categories as a taxonomy and abstraction layer takes this idea further. Unlike a typical functional program or library, the interaction trees framework need to support maintainable, composable, mechanized proofs. This is where the properties of category theoretic ideas truly shine.

**An alternative foundations for maths & computing**

This is where we get into exotic things like homotopy type theory, topoi, Curry-Howard-Lambek, etc. We're going to save all that for later.


# How well does category theory work in Coq?

That's a big question; let's break it down.

**How easy is it to construct a category in Coq?**

Using [Wiegley's library](https://github.com/jwiegley/category-theory), let's investigate the category of Coq types and functions. This category has `obj := Type`, `hom X Y := X -> Y`, `id X x := x`, and `compose g f x := g (f x)`.

The standard library provides named definitions for these things so there's very little work for us to do:

```coq
From Coq Require Import Setoid.

From Category Require Import Theory.

Definition MyCoqCategory: Category.
Proof.
    unshelve refine (
        Build_Category'
            (@Basics.arrow)
            (@Datatypes.id)
            (@Basics.compose)
    ) ; intros; try reflexivity.
    1: refine {|
        Setoid.equiv := fun f g => forall x, f x = g x
    |} ; constructor.
    all: cbv ; congruence.
Defined.
```

In my opinion, that definition counts as "easy."

However, that definition also isn't as awesome as one might initially hope. For instance, the following definition does not work:

```coq
(* The term "obj[MyCoqCategory]" has type "Type"
 * while it is expected to have type "obj[MyCoqCategory]"
 * (universe inconsistency: Cannot enforce MyCoqCategory.u0 <=
 * Basics.arrow.u0 because Basics.arrow.u0 < MyCoqCategory.u0).
 *)
Definition foo: obj[MyCoqCategory]
 := obj[MyCoqCategory]
.
```

The trouble is, Coq's universe system makes it impossible to define a category that's large enough to contain all Coq types.

This is actually a Good Thing for soundness reasons but it makes "programming in Coq with universal constructions" significantly less fun than one might initially hope. (This issue arises for many other categories you'd like to define & use, including the category of categories, certain functor categories, etc.)

_Conclusion_: it's easy to construct categories in Coq, as long as they are constructible.


**How easy is it to reason about categories in Coq?**

That depends on whether you are using a good library.

In category theory, most of the terms have dependent types:

* objects depend on the category they are sourced-from;
* arrows depend on their domain and codomain objects;
* functors depend on their domain and codomain categories;
* natural transformations depend on their domain and codomain functors;
* etc.

Category theory is all about _equation rewriting_. Unfortunately, rewriting does not always work smoothly with dependent types: the difference between _equal_ and _convertible_ is extremely relevant here and can make otherwise simple proofs tiresome and difficult to maintain.

Fortunately these issues can largely be managed by proof automation.