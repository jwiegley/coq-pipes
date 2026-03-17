From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Data.Functor.Identity.
Require Import P.Pipes.

Generalizable All Variables.

Section Bounded.

Variable n : nat.
Variable r : Type.
Variable d : r.

Context `{Monad m}.

(*
Instance Proxy_MonadTrans {a' a b' b} : MonadTrans (Proxy a' a b' b) :=
{ lift := fun m _ _ A => @M a' a b' b m r A id
}.

Instance Proxy_MonadTransLaws {a' a b' b} : MonadTrans (Proxy a' a b' b) :=
{ trans_law_1 := ;
  trans_law_2 :=
}.
*)

(*
Definition repeatM `(x : m a) : Producer' a m r :=
  fun _ _ => lift x >~ cat (n:=n) (d:=d).

replicateM :: Monad m => Int -> m a -> Producer' a m ()
replicateM n m = lift m >~ take n
*)

Definition drain {a} : Consumer' a m r :=
  fun _ _ => forP (cat (n:=n) (d:=d)) (fun _ => pure tt).

Definition map `(f : a -> b) :
  Pipe a b m r := forP (cat (n:=n) (d:=d)) (yield \o f).

(*
Definition mapM (f : a -> m b) : Pipe a b m r :=
  for cat $ fun a => do
    b <- lift (f a) ;;
    yield b.

listuence :: Monad m => Pipe (m a) a m r
listuence = mapM id
*)

Definition mapFoldable `(f : a -> list b) : Pipe a b m r :=
  forP (cat (n:=n) (d:=d)) (fun x => each (f x) (x':=unit) (x:=a)).

Definition filter `(p : a -> bool) : Pipe a a m r :=
  forP (cat (n:=n) (d:=d)) $ fun a => if p a then yield a else pure tt.

(*
filterM :: Monad m => (a -> m Bool) -> Pipe a a m r
filterM predicate = for cat $ \a -> do
    b <- lift (predicate a)
    when b (yield a)
*)

Fixpoint take (n' : nat) {a} : Pipe a a m unit :=
  match n' with
  | 0 => pure tt
  | S k => await >>= fun x => yield x >> take k
  end.

Fixpoint takeWhile `(p : a -> bool) {n : nat} {d : r} :
  Pipe a a m unit :=
  if n isn't S n' then Pure tt else
  await >>= fun a =>
  if p a
  then yield a >> takeWhile p (n:=n') (d:=d)
  else return_ tt.

Definition drop (n' : nat) {a} : Pipe a a m r :=
  (fix loop k := match k with
    | 0 => pure tt
    | S k' => await >>= fun _ => loop k'
    end) n' >> cat (n:=n) (d:=d).

Fixpoint dropWhile `(p : a -> bool) {n : nat} {d : r} :
  Pipe a a m r :=
  if n isn't S n' then Pure d else
  await >>= fun a =>
  if p a
  then dropWhile p (n:=n') (d:=d)
  else yield a >> cat (n:=n) (d:=d).

Definition concat {a} : Pipe (list a) a m r :=
  forP (cat (n:=n) (d:=d)) (fun xs => each xs (x':=unit) (x:=list a)).

Definition findIndices `(p : a -> bool) : Pipe a nat m r :=
  let fix loop i n :=
    if n isn't S n' then Pure d else
    await >>= fun a =>
    (if p a then yield i else pure tt) >>
    loop (i + 1) n' in
  loop 0 n.

Definition elemIndices {a} (eqb : a -> a -> bool) (x : a) :
  Pipe a nat m r :=
  findIndices (eqb x).

Definition scan `(step : x -> a -> x) (begin : x) `(done : x -> b) :
  Pipe a b m r :=
  let fix loop x n :=
    if n isn't S n' then Pure d else
    yield (done x) >>
    (await >>= fun a =>
    let x' := step x a in
    loop x' n') in
  loop begin n.

(*
scanM :: Monad m => (x -> a -> m x) -> m x -> (x -> m b) -> Pipe a b m r
scanM step begin done = do
    x <- lift begin
    loop x
  where
    loop x = do
        b <- lift (done x)
        yield b
        a  <- await
        x' <- lift (step x a)
        loop $! x'

chain :: Monad m => (a -> m ()) -> Pipe a a m r
chain f = for cat $ \a -> do
    lift (f a)
    yield a
*)

Definition fold `(step : x -> a -> x) (begin : x) `(done : x -> b)
  (p0 : Producer a m unit) : m b :=
  let fix loop p x := match p with
    | Request v  _  => False_rect _ v
    | Respond a  fu => loop (fu tt) (step x a)
    | M g  h  => h >>= fun p' => loop (g p') x
    | Pure    _     => return_ (done x)
    end in
  loop p0 begin.

Definition fold' `(step : x -> a -> x) (begin : x) `(done : x -> b)
  (p0 : Producer a m r) : m (b * r)%type :=
  let fix loop p x := match p with
    | Request v  _  => False_rect _ v
    | Respond a  fu => loop (fu tt) (step x a)
    | M g  h  => h >>= fun p' => loop (g p') x
    | Pure    r     => return_ (done x, r)
    end in
  loop p0 begin.

Definition foldM
  `(step : x -> a -> m x) (begin : m x) `(done : x -> m b)
  (p0 : Producer a m unit) : m b :=
  let fix loop p x := match p with
    | Request v  _  => False_rect _ v
    | Respond a  fu =>
          step x a >>= fun x' =>
          loop (fu tt) x'
    | M g  h  => h >>= fun p' => loop (g p') x
    | Pure    _     => done x
    end in
  begin >>= fun x0 =>
  loop p0 x0.

Definition foldM'
  `(step : x -> a -> m x) (begin : m x) `(done : x -> m b)
  (p0 : Producer a m r) : m (b * r)%type :=
  let fix loop p x := match p with
    | Request v  _  => False_rect _ v
    | Respond a  fu =>
          step x a >>= fun x' =>
          loop (fu tt) x'
    | M g  h  => h >>= fun p' => loop (g p') x
    | Pure    r     =>
          done x >>= fun b =>
          return_ (b, r)
    end in
  begin >>= fun x0 =>
  loop p0 x0.

Definition null {a} (p : Producer a m unit) : m bool :=
  let fix go (p : Producer a m unit) : m bool :=
    match p with
    | Request v _  => False_rect _ v
    | Respond _ fu => return_ false
    | M g h  => h >>= (go \o g)
    | Pure   _     => return_ true
    end in
  go p.

Definition all `(p : a -> bool) (p0 : Producer a m unit) : m bool :=
  null (p0 >-> (filter (fun a => ~~ (p a)) >> return_ tt)).

Definition any `(p : a -> bool) (p0 : Producer a m unit) : m bool :=
  fmap negb (null (p0 >-> (filter p >> return_ tt))).

Definition and : Producer bool m unit -> m bool := all id.

Definition or : Producer bool m unit -> m bool := any id.

Definition elem {a} (eqb : a -> a -> bool) (x : a) :
  Producer a m unit -> m bool :=
  any (eqb x).

Definition notElem {a} (eqb : a -> a -> bool) (x : a) :
  Producer a m unit -> m bool :=
  all (negb \o eqb x).

Definition head {a} (p : Producer a m unit) : m (Maybe a) :=
  let fix go (p : Producer a m unit) : m (Maybe a) :=
    match p with
    | Request v _  => False_rect _ v
    | Respond x fu => return_ (Just x)
    | M g h  => h >>= (go \o g)
    | Pure   _     => return_ Nothing
    end in
  go p.

Definition find `(p : a -> bool) (p0 : Producer a m unit) :
  m (Maybe a) :=
  head (p0 >-> (filter p >> return_ tt)).

Definition findIndex `(p : a -> bool) (p0 : Producer a m unit) :
  m (Maybe nat) :=
  head (p0 >-> (findIndices p >> return_ tt)).

Definition index (n : nat) `(p : Producer a m unit) : m (Maybe a) :=
  head (p >-> (drop n >> return_ tt)).

Definition last {a} (p0 : Producer a m unit) : m (Maybe a) :=
  let fix next' (p : Producer a m unit) :
    m (Either unit (a * Producer a m unit)) :=
    match p with
    | Request v _  => False_rect _ v
    | Respond x fu => return_ $ Right (x, fu tt)
    | M g h  => h >>= (next' \o g)
    | Pure   _     => return_ $ Left tt
    end in
  let fix loop z k (p : Producer a m unit) : m (Maybe a) :=
    if k isn't S k' then return_ Nothing else
    next' p >>= fun x =>
    match x with
    | Left   _       => return_ (Just z)
    | Right (a', p') => loop a' k' p'
    end in
  next' p0 >>= fun x =>
  match x with
  | Left   _      => return_ Nothing
  | Right (a', p') => loop a' n p'
  end.

Definition length {a} : Producer a m unit -> m nat :=
  fold (fun n _ => n + 1) 0 id.

Definition maximum : Producer nat m unit -> m (Maybe nat) :=
  let step x z := Just (match x with
    | Nothing => z
    | Just a' => max z a'
    end) in
  fold step Nothing id.

Definition minimum : Producer nat m unit -> m (Maybe nat) :=
  let step x z := Just (match x with
    | Nothing => z
    | Just a' => min z a'
    end) in
  fold step Nothing id.

Definition sum : Producer nat m unit -> m nat :=
  fold plus 0 id.

Definition product : Producer nat m unit -> m nat :=
  fold mult 1 id.

(* This is the version of toListM defined by the pipes library, but it is not
   very amenable to proof. *)

Definition toListM_fold {a} : Producer a m unit -> m (list a) :=
  let step x a := x \o (cons a) in
  let begin    := id in
  let done x   := x nil in
  fold step begin done.

Fixpoint toListM `(p : Producer a m unit) : m (list a) :=
  match p with
  | Request v _  => False_rect _ v
  | Respond x fu => cons x <$> toListM (fu tt)
  | M f t  => t >>= (toListM \o f)
  | Pure    _    => pure nil
  end.

End Bounded.

Fixpoint toList (n : nat) {a} (p : Producer a id unit) : list a :=
  if n isn't S n' then nil else
  match p with
  | Request v _  => False_rect _ v
  | Respond a fu => a :: toList n' (fu tt)
  | M g h  => h >>= (toList n' \o g)
  | Pure    _    => nil
  end.

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
  rewrite /map /cat /yield /comp.
  move: (pull tt).
  reduce_proxy IHx (rewrite /= /comp);
  try move/functional_extensionality in IHx;
  assume_infinity.
  - rewrite E in IHx.
    by rewrite IHx; congr (Request _ _).
  - rewrite /connect /= Hpull.
    congr (Respond _ _).
    rewrite IHx /connect.
    extensionality u; case: u.
    rewrite E -Hpull /=.
    congr (_ +>> _).
    extensionality v; by case: v.
  - rewrite E in IHx.
    rewrite IHx /connect /= Hpull.
    by congr (M _ _).
  - by rewrite /connect /=.
Qed.

(*
filter (pure True) = cat
filter (liftA2 (&&) p1 p2) = filter p1 >-> filter p2

take 0 = return ()
take (m + n) = take m >> take n
take <infinity> = cat
take (min m n) = take m >-> take n

takeWhile (pure True) = cat
takeWhile (liftA2 (&&) p1 p2) = takeWhile p1 >-> takeWhile p2

drop 0 = cat
drop (m + n) = drop m >-> drop n

dropWhile (pure False) = cat
dropWhile (liftA2 (||) p1 p2) = dropWhile p1 >-> dropWhile p2
*)

Theorem toListM_each_id : forall a,
  toListM \o (fun xs => each (x':=False) (x:=unit) xs) =1 pure (a:=list a).
Proof. by move=> ?; elim=> //= [? ? ->]. Qed.

End PipesLawsPrelude.
