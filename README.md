# Proof of the Pipes Laws

This is a formalization in Coq of the Haskell
[pipes](http://hackage.haskell.org/package/pipes) library. Nearly all its
functions have been implemented, and the laws mentioned in the documentation
proven. It relies on the
[coq-haskell](https://github.com/jwiegley/coq-haskell) project, whose aim is
to simplify both the transcoding of Haskell types and functions into Coq, and
the extraction of proven algorithms back into Haskell.

Much gratitude is given to Gabriel Gonzalez for dialoging with me about this
project over the long months of its inception, and for his
[manual proofs](http://www.haskellforall.com/2013/10/manual-proofs-for-pipes-laws.html)
of the laws, which were an excellent reference. Thanks are also due to Paolo
Capriotti and Dan Burton, with whom I never interacted, but who where the
spiritual fathers of this formalization effort.

## Laws proven

**43** laws were proven, with 7 requiring a compromise documented below. These
  are indicated with **bolded** leaders in the following list. All of them are
  proofs involving the functions `push` or `pull`.

### Klesli category

- Obligation [`functor_1`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Internal.v#95)
- Obligation [`functor_2`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Internal.v#96)

- Obligation [`applicative_1`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Internal.v#100)
- Obligation [`applicative_2`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Internal.v#101)    (* 3-5 proven by inference *)

- Obligation [`monad_1`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Internal.v#109)
- Obligation [`monad_2`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Internal.v#110)
- Obligation [`monad_4`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Internal.v#111)          (* 3 proven by inference *)

### Respond category

- Theorem [`respond_distrib`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#184) : `(f >=> g) />/ h = (f />/ h) >=> (g />/ h)`

- Obligation [`(* Right identity: Respond *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#201)
- Obligation [`(* Left identity: Respond *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#205)
- Obligation [`(* Associativity: Respond *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#208)

- Corollary [`respond_zero`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#213) : `pure />/ f = pure`

### Request category

- Theorem [`request_distrib`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#226) : `h \>\ (f >=> g) = (h \>\ f) >=> (h \>\ g)`

- Obligation [`(* Right identity: Request *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#243)
- Obligation [`(* Left identity: Request *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#246)
- Obligation [`(* Associativity: Request *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#249)

- Corollary [`request_zero`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#254) : `f \>\ pure = pure`

### Push category

- Lemma [`push_request`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#292) : `Request x g >>~ f = Request x (g >~> f)`
- Lemma [`push_m`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#298) : `M g h >>~ f = M (g >~> f) h`

- **Obligation** [`(* Right identity: Push *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#312)
- **Obligation** [`(* Left identity: Push *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#321)
- Obligation [`(* Associativity: Push *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#331)

### Pull category

- Lemma [`pull_respond`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#358) : `f +>> Respond x g = Respond x (f >+> g)`
- Lemma [`pull_m`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#364) : `f +>> M g h = M (f >+> g) h`

- **Obligation** [`(* Right identity: Pull *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#378)
- **Obligation** [`(* Left identity: Pull *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#388)
- Obligation [`(* Associativity: Pull *)`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#399)

- **Theorem** [`push_pull_assoc`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#418) : `(f >+> g) >~> h = f >+> (g >~> h)`

### Duals

- Theorem [`request_id`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#453)       : `reflect \o request = respond`
- Theorem [`reflect_distrib`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#456)  : `reflect (f x >>= g) = reflect (f x) >>= (reflect \o g)`
- Theorem [`request_comp`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#466)     : `reflect \o (f \>\ g) = (reflect \o g) />/ (reflect \o f)`
- Theorem [`respond_id`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#475)       : `reflect \o respond = request`
- Theorem [`respond_comp`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#478)     : `reflect \o (f />/ g) = (reflect \o g) \>\ (reflect \o f)`
- Corollary [`distributivity`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#496) : `reflect \o (f >=> g) = (reflect \o f) >=> (reflect \o g)`
- Theorem [`zero_law`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#502)         : `reflect \o pure = pure`
- Theorem [`involution`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Core.v#505)       : `reflect \o reflect = id`

### General theorems

- Theorem [`for_yield_f`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes.v#72)   : `forP (yield x) f = f x`
- Theorem [`for_yield`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes.v#81)     : `forP s yield = s`
- Theorem [`nested_for_a`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes.v#90)  : `forP s (fun a => forP (f a) g) = forP (forP s f) g`
- Theorem [`nested_for_b`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes.v#104) : `forP (forP s f) g = forP s (f />/ g)`

### Prelude functions

- **Theorem** [`map_id`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Prelude.v#351)           : `map id = cat`
- **Theorem** [`map_compose`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Prelude.v#360)      : `map (g \o f) = map f >-> map g`

- Theorem [`toListM_each_id`](https://github.com/jwiegley/coq-pipes/blob/master/src/Pipes/Prelude.v#387)  : `toListM \o each = pure`

## The Compromise

`push` and `pull` are necessarily infinite functions. However, representing
them as co-fixpoints makes some other things impossible (for example,
`runEffect` must be a fixpoint). So rather than splitting up the development,
a balance was struck. This compromise is three-fold:

  1. `push` and `pull` are implemented in terms of "fuel". When fuel
     is exhausted, they return `Pure someDefault`.

  2. An axiom is added such that there is always fuel (i.e., `fuel > 0`).

  3. A second axiom is added to assert that a "step" of `push` or `pull`
     at fuel `N` behaves identically to that at fuel `N+1`. (i.e.,
     `forall n, n > 0 -> push (fuel:=n) = push (fuel:=n.+1)`)

This allows `push` and `pull` to be defined inductively, but used in a context
where the "base case" cannot be reached, making them infinite for the purposes
of proof.

## History of this work

**2013 Oct 6**, Gabriel made his hand-written proofs of the `pipes` laws
public. Dan Burton commented that someone should mechanize them in Agda.
Gabriel mentioned he had started down that road already, with help from Paolo
Capriotti.

**2013 Oct 7**, I also began trying to encode the laws in Agda, so Gabriel and
I began discussing the problems of strict positivity regarding the `Proxy`
type.

**2014 Nov 16**, after letting the project lie for a while, I started playing
around with teasing `Proxy` into a functor `ProxyF` under the free monad.
Gabriel tells me this is exactly what `pipes` 2.4.0 did, so with that
confirmation I started down the road of how to encode free monads in Coq. I
made the switch to Coq after being inspired by talks at
[OPLSS 2014](https://www.cs.uoregon.edu/research/summerschool/summer14/curriculum.html),
and because I was using it for a large project at work.

Over the next few months I read several papers by Conor McBride suggesting the
use of *container types*, even
[formalizing](https://github.com/jwiegley/coq-haskell/blob/master/research/Conor.v)
most of his paper
[Kleisli Arrows of Outrageous Fortune](https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf).
This, plus
[comments](https://github.com/jwiegley/notes/blob/master/agda-free-monad-trick.md)
made by [Paolo Capriotti](http://www.paolocapriotti.com), gave me much food
for thought, although little code was written.

Around **2015 Mar 1** I read an old paper by
[Venanzio Capretta](http://www.duplavis.com/venanzio/) on
[Universal Algebra in Type Theory](http://www.duplavis.com/venanzio/publications/Universal_Algebra_TPHOLs_1999.pdf)
which made container types far more comprehensible to me, thus energizing me
to consider this project again.

**2015 May 30**, After a few weeks of trying various free monad encodings
based on container types and universal algebra, I stumbled across a trick
Edward Kmett used for his
[Boehm-Berarducci encoding of the free monad transformer](https://github.com/ekmett/free/issues/86).
It turns out that although he did this to improve GHC roles for an applied
functor, it also solves the strict positivity issue in Coq!

**2015 May 31**, With this trick in hand, I was able to transcode most of the
`pipes` library directly from Haskell, requiring only minor syntactic
variations to adapt it to the Gallina language. With those done, the laws were
relatively easy, falling into place over a two week period.

**2015 Jun 12**, all of the laws are complete.

So in all it took 1.5 years to learn Coq well enough and to find the right
abstraction, and 2 weeks to do the actual work.

