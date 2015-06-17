Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Identity.
Require Import P.Pipes.

Generalizable All Variables.

Fixpoint toListM `{Monad m} `(p : Producer a m unit) : m (seq a) :=
  match p with
  | Request v _  => False_rect _ v
  | Respond x fu => cons x <$> toListM (fu tt)
  | M _     f t  => t >>= (toListM \o f)
  | Pure    _    => pure [::]
  end.

Section Bounded.

Variable n : nat.
Variable r : Type.
Variable d : r.

Definition map `{Monad m} `(f : a -> b) :
  Pipe a b m r := forP (cat (n:=n) (d:=d)) (yield \o f).

End Bounded.

Arguments map {n r d m H a b} f.

Module PipesLawsPrelude.

Include PipesLaws.
Include Compromise.

Require Import FunctionalExtensionality.

Theorem map_id : forall a,
  map (n:=n) (d:=d) (@id a) = cat (n:=n) (d:=d).
Proof.
  move=> ?.
  rewrite /map /cat /yield /respond /forP.
  move: (pull tt).
  by reduce_proxy IHx (rewrite /bind /=).
Qed.

Theorem map_compose `{MonadLaws m} : forall `(f : a -> b) `(g : b -> c),
    map (n:=n) (d:=d) (g \o f)
      = map (n:=n) (d:=d) f >-> map (n:=n) (d:=d) g.
Proof.
  move=> *.
  rewrite /map /cat /yield /funcomp.
  move: (pull tt).
  reduce_proxy IHx (rewrite /= /funcomp);
  try move/functional_extensionality in IHx;
  assume_infinity.
  - rewrite E in IHx.
    rewrite IHx.
    congr (Request _ _).
    rewrite IHx /bind /= /connect /=.
    congr (Respond _ _).
    rewrite /funcomp /=.
    extensionality t.
    congr (_ <<+ _).
    extensionality u.
    by case: t; case: u.
  - case: t.
    by rewrite E -Hpull.
  - rewrite E in IHx.
    rewrite IHx.
    by congr (M _ _).
Qed.

Theorem toListM_each_id : forall a, toListM \o each =1 pure (a:=seq a).
Proof. by move=> ?; elim=> //= [? ? ->]. Qed.

End PipesLawsPrelude.
