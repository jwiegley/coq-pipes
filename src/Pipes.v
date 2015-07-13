Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Identity.
Require Export P.Pipes.Core.
Require Export P.Pipes.Internal.

Generalizable All Variables.

Definition yield {a x' x m} (z : a) : Proxy x' x unit a m unit :=
  let go : Producer' a m unit := fun _ _ => respond z in @go x' x.

Notation "f ~> g" := (f />/ g) (at level 70).
Notation "f <~ g" := (g ~> f) (at level 70).

Definition await {a y' y m} : Proxy unit a y' y m a :=
  let go : Consumer' a m a := fun _ _ => request tt in @go y' y.

Notation "x >~ y" := ((fun _ : unit => x) >\\ y) (at level 70).
Notation "x ~< y" := (y >~ x) (at level 70).

Section Cat.

Variable n : nat.
Variable r : Type.
Variable d : r.

Definition cat `{Monad m} {a} : Pipe a a m r :=
  pull (n:=n) (default:=d) tt.

End Cat.

Arguments cat {n r d m H a}.

Definition connect `{Monad m} `(p1 : Proxy a' a unit b m r)
  `(p2 : Proxy unit b c' c m r) : Proxy a' a c' c m r :=
  (fun _ : unit => p1) +>> p2.

Notation "x >-> y" := (connect x y) (at level 60).
Notation "x <-< y" := (y >-> x) (at level 60).

Fixpoint next `{Monad m} `(p : Producer a m r) :
  m (Either r (a * Producer a m r)) :=
  match p with
  | Request v _  => False_rect _ v
  | Respond a fu => return_ $ Right (a, fu tt)
  | M _     g h  => h >>= (next \o g)
  | Pure    r    => return_ $ Left r
  end.

Definition each `{Monad m} {a} (xs : seq a) : Producer' a m unit :=
  fun _ _ => mapM_ yield xs.
Arguments each {m _ a} xs {_ _}.

Definition discard `{Monad m} {a} : a -> m unit := fun _ => return_ tt.

Definition every `{Monad m} `(xs : seq a) : Producer' a m unit :=
  fun _ _ => foldM (const yield) tt xs.
Arguments every {m _ a} xs {_ _}.

(****************************************************************************
 *
 * General theorems about functions in the pipes library.
 *)

Module PipesLaws.

Include PipesLawsCore.

Require Import FunctionalExtensionality.

(* Looping over a single yield simplifies to function application *)
Theorem for_yield_f `{MonadLaws m} :
  forall `(f : b -> Proxy x' x c' c m unit) x,
    forP (yield x) f = f x.
Proof.
  move=> *.
  by rewrite /yield /respond /= /bind /funcomp join_fmap_pure_x.
Qed.

(* Re-yielding every element of a stream returns the original stream *)
Theorem for_yield `{MonadLaws m} : forall `(s : Proxy x' x unit b m unit),
  forP s yield = s.
Proof.
  move=> ? ? ?.
  by reduce_proxy IHx (rewrite /yield /respond /= /bind /=).
Qed.

(* Nested for loops can become a sequential for loops if the inner loop
   body ignores the outer loop variable *)
Theorem nested_for_a `{MonadLaws m} :
  forall `(s : Proxy x' x b' b m a')
         `(f : b -> Proxy x' x c' c m b')
         `(g : c -> Proxy x' x d' d m c'),
    forP s (fun a => forP (f a) g) = forP (forP s f) g.
Proof.
  move=> ? ? ? ? ? s *.
  move: s.
  reduce_proxy IHx simpl.
  rewrite respond_distrib.
  move/functional_extensionality in IHx.
  by rewrite -IHx.
Qed.

Theorem nested_for_b `{MonadLaws m} :
  forall `(s : Proxy x' x b' b m a')
         `(f : b -> Proxy x' x c' c m b')
         `(g : c -> Proxy x' x d' d m c'),
    forP (forP s f) g = forP s (f />/ g).
Proof.
  move=> ? ? ? ? ? s *.
  move: s.
  reduce_proxy IHx simpl.
  rewrite respond_distrib.
  move/functional_extensionality in IHx.
  by rewrite IHx.
Qed.

End PipesLaws.
