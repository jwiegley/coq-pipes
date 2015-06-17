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
Definition repeatM `{Monad m} `(x : m a) : Producer' a m r :=
  fun _ _ => lift x >~ cat (n:=n) (d:=d).

replicateM :: Monad m => Int -> m a -> Producer' a m ()
replicateM n m = lift m >~ take n
*)

Definition drain `{Monad m} {a} : Consumer' a m r :=
  fun _ _ => forP (cat (n:=n) (d:=d)) discard.

Definition map `{Monad m} `(f : a -> b) :
  Pipe a b m r := forP (cat (n:=n) (d:=d)) (yield \o f).

(*
Definition mapM `{Monad m} (f : a -> m b) : Pipe a b m r :=
  for cat $ fun a => do
    b <- lift (f a) ;;
    yield b.

sequence :: Monad m => Pipe (m a) a m r
sequence = mapM id
*)

Definition mapFoldable `{Monad m} `(f : a -> seq b) : Pipe a b m r :=
  forP (cat (n:=n) (d:=d)) (fun x => each (f x) (x':=unit) (x:=a)).

Definition filter `{Monad m} `(p : a -> bool) : Pipe a a m r :=
  forP (cat (n:=n) (d:=d)) $ fun a => when (p a) (yield a).

(*
filterM :: Monad m => (a -> m Bool) -> Pipe a a m r
filterM predicate = for cat $ \a -> do
    b <- lift (predicate a)
    when b (yield a)
*)

Definition take `{Monad m} (n' : nat) {a} : Pipe a a m unit :=
  replicateM_ n' (await >>= yield).

(*
takeWhile :: Monad m => (a -> Bool) -> Pipe a a m ()
takeWhile predicate = go
  where
    go = do
        a <- await
        if (predicate a)
            then do
                yield a
                go
            else return ()

drop :: Monad m => Int -> Pipe a a m r
drop n = do
    replicateM_ n await
    cat

dropWhile :: Monad m => (a -> Bool) -> Pipe a a m r
dropWhile predicate = go
  where
    go = do
        a <- await
        if (predicate a)
            then go
            else do
                yield a
                cat

concat :: (Monad m, Foldable f) => Pipe (f a) a m r
concat = for cat each

elemIndices :: (Monad m, Eq a) => a -> Pipe a Int m r
elemIndices a = findIndices (a ==)

findIndices :: Monad m => (a -> Bool) -> Pipe a Int m r
findIndices predicate = loop 0
  where
    loop n = do
        a <- await
        when (predicate a) (yield n)
        loop $! n + 1

scan :: Monad m => (x -> a -> x) -> x -> (x -> b) -> Pipe a b m r
scan step begin done = loop begin
  where
    loop x = do
        yield (done x)
        a <- await
        let x' = step x a
        loop $! x'

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

fold :: Monad m => (x -> a -> x) -> x -> (x -> b) -> Producer a m () -> m b
fold step begin done p0 = loop p0 begin
  where
    loop p x = case p of
        Request v  _  -> closed v
        Respond a  fu -> loop (fu ()) $! step x a
        M          m  -> m >>= \p' -> loop p' x
        Pure    _     -> return (done x)

fold' :: Monad m => (x -> a -> x) -> x -> (x -> b) -> Producer a m r -> m (b, r)
fold' step begin done p0 = loop p0 begin
  where
    loop p x = case p of
        Request v  _  -> closed v
        Respond a  fu -> loop (fu ()) $! step x a
        M          m  -> m >>= \p' -> loop p' x
        Pure    r     -> return (done x, r)

foldM
    :: Monad m
    => (x -> a -> m x) -> m x -> (x -> m b) -> Producer a m () -> m b
foldM step begin done p0 = do
    x0 <- begin
    loop p0 x0
  where
    loop p x = case p of
        Request v  _  -> closed v
        Respond a  fu -> do
            x' <- step x a
            loop (fu ()) $! x'
        M          m  -> m >>= \p' -> loop p' x
        Pure    _     -> done x

foldM'
    :: Monad m
    => (x -> a -> m x) -> m x -> (x -> m b) -> Producer a m r -> m (b, r)
foldM' step begin done p0 = do
    x0 <- begin
    loop p0 x0
  where
    loop p x = case p of
        Request v  _  -> closed v
        Respond a  fu -> do
            x' <- step x a
            loop (fu ()) $! x'
        M          m  -> m >>= \p' -> loop p' x
        Pure    r     -> do
            b <- done x
            return (b, r)

all :: Monad m => (a -> Bool) -> Producer a m () -> m Bool
all predicate p = null $ p >-> filter (\a -> not (predicate a))

any :: Monad m => (a -> Bool) -> Producer a m () -> m Bool
any predicate p = liftM not $ null (p >-> filter predicate)

and :: Monad m => Producer Bool m () -> m Bool
and = all id

or :: Monad m => Producer Bool m () -> m Bool
or = any id

elem :: (Monad m, Eq a) => a -> Producer a m () -> m Bool
elem a = any (a ==)

notElem :: (Monad m, Eq a) => a -> Producer a m () -> m Bool
notElem a = all (a /=)

find :: Monad m => (a -> Bool) -> Producer a m () -> m (Maybe a)
find predicate p = head (p >-> filter predicate)

findIndex :: Monad m => (a -> Bool) -> Producer a m () -> m (Maybe Int)
findIndex predicate p = head (p >-> findIndices predicate)

head :: Monad m => Producer a m () -> m (Maybe a)
head p = do
    x <- next p
    return $ case x of
        Left   _     -> Nothing
        Right (a, _) -> Just a

index :: Monad m => Int -> Producer a m () -> m (Maybe a)
index n p = head (p >-> drop n)

last :: Monad m => Producer a m () -> m (Maybe a)
last p0 = do
    x <- next p0
    case x of
        Left   _      -> return Nothing
        Right (a, p') -> loop a p'
  where
    loop a p = do
        x <- next p
        case x of
            Left   _       -> return (Just a)
            Right (a', p') -> loop a' p'

length :: Monad m => Producer a m () -> m Int
length = fold (\n _ -> n + 1) 0 id

maximum :: (Monad m, Ord a) => Producer a m () -> m (Maybe a)
maximum = fold step Nothing id
  where
    step x a = Just $ case x of
        Nothing -> a
        Just a' -> max a a'

minimum :: (Monad m, Ord a) => Producer a m () -> m (Maybe a)
minimum = fold step Nothing id
  where
    step x a = Just $ case x of
        Nothing -> a
        Just a' -> min a a'

null :: Monad m => Producer a m () -> m Bool
null p = do
    x <- next p
    return $ case x of
        Left  _ -> True
        Right _ -> False

sum :: (Monad m, Num a) => Producer a m () -> m a
sum = fold (+) 0 id

product :: (Monad m, Num a) => Producer a m () -> m a
product = fold ( * ) 1 id

toList :: Producer a Identity () -> [a]
toList = loop
  where
    loop p = case p of
        Request v _  -> closed v
        Respond a fu -> a:loop (fu ())
        M         m  -> loop (runIdentity m)
        Pure    _    -> []

toListM :: Monad m => Producer a m () -> m [a]
toListM = fold step begin done
  where
    step x a = x . (a:)
    begin = id
    done x = x []

zip :: Monad m
    => (Producer   a     m r)
    -> (Producer      b  m r)
    -> (Producer' (a, b) m r)
zip = zipWith (,)

zipWith :: Monad m
    => (a -> b -> c)
    -> (Producer  a m r)
    -> (Producer  b m r)
    -> (Producer' c m r)
zipWith f = go
  where
    go p1 p2 = do
        e1 <- lift $ next p1
        case e1 of
            Left r         -> return r
            Right (a, p1') -> do
                e2 <- lift $ next p2
                case e2 of
                    Left r         -> return r
                    Right (b, p2') -> do
                        yield (f a b)
                        go p1' p2'

tee :: Monad m => Consumer a m r -> Pipe a a m r
tee p = evalStateP Nothing $ do
    r <- up >\\ (hoist lift p //> dn)
    ma <- lift get
    case ma of
        Nothing -> return ()
        Just a  -> yield a
    return r
  where
    up () = do
        ma <- lift get
        case ma of
            Nothing -> return ()
            Just a  -> yield a
        a <- await
        lift $ put (Just a)
        return a
    dn v = closed v

generalize :: Monad m => Pipe a b m r -> x -> Proxy x a x b m r
generalize p x0 = evalStateP x0 $ up >\\ hoist lift p //> dn
  where
    up () = do
        x <- lift get
        request x
    dn a = do
        x <- respond a
        lift $ put x
*)

Fixpoint toListM `{Monad m} `(p : Producer a m unit) : m (seq a) :=
  match p with
  | Request v _  => False_rect _ v
  | Respond x fu => cons x <$> toListM (fu tt)
  | M _     f t  => t >>= (toListM \o f)
  | Pure    _    => pure [::]
  end.

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

Theorem toListM_each_id : forall a,
  toListM \o (fun xs => each (x':=False) (x:=unit) xs) =1 pure (a:=seq a).
Proof. by move=> ?; elim=> //= [? ? ->]. Qed.

End PipesLawsPrelude.
