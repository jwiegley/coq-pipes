Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Identity.

Generalizable All Variables.

(****************************************************************************
 *
 * Proxy
 *)

Inductive Proxy (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
  | Request of a' & (a  -> Proxy a' a b' b m r)
  | Respond of b  & (b' -> Proxy a' a b' b m r)
  | M : forall x, (x -> Proxy a' a b' b m r) -> m x -> Proxy a' a b' b m r
  | Pure of r.

Arguments Request {a' a b' b m r} _ _.
Arguments Respond {a' a b' b m r} _ _.
Arguments M {a' a b' b m r x} _ _.
Arguments Pure {a' a b' b m r} _.

(****************************************************************************
 *
 * Fundamental code to operate with Proxy
 *)

Definition foldProxy `{Monad m}
  `(ka : a' -> (a  -> s) -> s)
  `(kb : b  -> (b' -> s) -> s)
  `(km : forall x, (x -> s) -> m x -> s)
  `(kp : r -> s)
  (p : Proxy a' a b' b m r) : s :=
  let fix go p := match p with
    | Request a' fa  => ka a' (go \o fa)
    | Respond b  fb' => kb b  (go \o fb')
    | M _     g  h   => km _  (go \o g) h
    | Pure    r      => kp r
    end in
  go p.

(* This is equivalent to [foldProxy Request Respond (fun _ => M)], but using
   that definition makes some proofs harder. *)
Definition Proxy_bind {a' a b' b c d} `{Monad m}
  (f : c -> Proxy a' a b' b m d) (p0 : Proxy a' a b' b m c) :
  Proxy a' a b' b m d :=
  let fix go p := match p with
    | Request a' fa  => Request a' (go \o fa)
    | Respond b  fb' => Respond b  (go \o fb')
    | M _     f  t   => M (go \o f) t
    | Pure    r      => f r
    end in
  go p0.

(* The proofs of these laws are below. *)
Instance Proxy_Functor `{Monad m} {a' a b' b} :
  Functor (Proxy a' a b' b m) := {
  fmap := fun _ _ f => Proxy_bind (Pure \o f)
}.

Instance Proxy_Applicative `{Monad m} {a' a b' b} :
  Applicative (Proxy a' a b' b m) := {
  pure := fun _ => Pure;
  ap   := fun _ _ pf px => Proxy_bind (fmap ^~ px) pf
}.

Instance Proxy_Monad `{Monad m} {a' a b' b} :
  Monad (Proxy a' a b' b m) := {
  join := fun _ => Proxy_bind id
}.

Module PipesLawsInternal.

Include MonadLaws.

Require Import FunctionalExtensionality.

Tactic Notation "reduce_proxy" ident(IHu) tactic(T) :=
  elim=> [? ? IHu|? ? IHu|? ? IHu| ?]; T;
  try (try move => m0; f_equal; extensionality RP_A; exact: IHu).

(****************************************************************************
 *
 * Kleisli Category for Proxy a' a b' b m
 *)

Program Instance Proxy_FunctorLaws `{MonadLaws m} {a' a b' b} :
  FunctorLaws (Proxy a' a b' b m).
Obligation 1. by reduce_proxy IHx simpl. Qed.
Obligation 2. by reduce_proxy IHx simpl. Qed.

Program Instance Proxy_ApplicativeLaws `{MonadLaws m} {a' a b' b} :
  ApplicativeLaws (Proxy a' a b' b m).
Obligation 1. by reduce_proxy IHx simpl. Qed.
Obligation 2.
  move: u; reduce_proxy IHu (rewrite /funcomp /= /funcomp).
  move: v; reduce_proxy IHv (rewrite /funcomp /= /funcomp).
  by move: w; reduce_proxy IHw simpl.
Qed.

Program Instance Proxy_MonadLaws `{MonadLaws m} {a' a b' b} :
  MonadLaws (Proxy a' a b' b m).
Obligation 1. by reduce_proxy IHx simpl. Qed.
Obligation 2. by reduce_proxy IHx simpl. Qed.
Obligation 4. by reduce_proxy IHx simpl. Qed.

End PipesLawsInternal.