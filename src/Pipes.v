Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Identity.
Require Export P.Pipes.Core.
Require Export P.Pipes.Internal.

Generalizable All Variables.

Fixpoint next `{Monad m} `(p : Producer a m r) :
  m (Either r (a * Producer a m r)) :=
  match p with
  | Request v _  => False_rect _ v
  | Respond a fu => return_ $ Right (a, fu tt)
  | M _     g h  => h >>= (next \o g)
  | Pure    r    => return_ $ Left r
  end.

Definition each `{Monad m} {a} : seq a -> Producer a m unit := mapM_ yield.

Definition discard `{Monad m} {a} : a -> m unit := fun _ => return_ tt.

Definition every `{Monad m} `(xs : seq a) : Producer' a m unit :=
  fun _ _ => foldM (const yield) tt xs.

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
  move=> ? ? ? ? ? f x.
  by rewrite /yield /respond /= /bind /funcomp join_fmap_pure_x.
Qed.

(* Re-yielding every element of a stream returns the original stream *)
Theorem for_yield `{MonadLaws m} : forall `(s : Proxy x' x unit b m unit),
  forP s yield = s.
Proof.
  move=> ? ? ?.
  by reduce_proxy IHx (rewrite /yield /respond /= /bind /= /funcomp).
Qed.

(* Nested for loops can become a sequential for loops if the inner loop
   body ignores the outer loop variable *)
Theorem nested_for_a `{MonadLaws m} :
  forall `(s : Proxy x' x b' b m a')
         `(f : b -> Proxy x' x c' c m b')
         `(g : c -> Proxy x' x d' d m c'),
    forP s (fun a => forP (f a) g) = forP (forP s f) g.
Proof.
  move=> x' x b' b a' s c' c f d' d g.
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
  move=> x' x b' b a' s c' c f d' d g.
  move: s.
  reduce_proxy IHx simpl.
  rewrite respond_distrib.
  move/functional_extensionality in IHx.
  by rewrite IHx.
Qed.

End PipesLaws.
