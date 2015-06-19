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

Fixpoint takeWhile `{Monad} `(p : a -> bool) {n : nat} {d : r} :
  Pipe a a m unit :=
  if n isn't S n' then Pure tt else
  a <-- await ;;
  if p a
  then yield a >> takeWhile p (n:=n') (d:=d)
  else return_ tt.

Definition drop `{Monad m} (n : nat) {a} : Pipe a a m r :=
  replicateM_ n (await >> return_ tt) ;;
  cat (n:=n) (d:=d).

Fixpoint dropWhile `{Monad m} `(p : a -> bool) {n : nat} {d : r} :
  Pipe a a m r :=
  if n isn't S n' then Pure d else
  a <-- await ;;
  if p a
  then dropWhile p (n:=n') (d:=d)
  else yield a >> cat (n:=n) (d:=d).

Definition concat `{Monad m} {a} : Pipe (seq a) a m r :=
  forP (cat (n:=n) (d:=d)) (fun xs => each xs (x':=unit) (x:=seq a)).

Fixpoint findIndices `{Monad m} `(p : a -> bool) : Pipe a nat m r :=
  let fix loop i n :=
    if n isn't S n' then Pure d else
    a <-- await ;;
    when (p a) (yield i) ;;
    loop (i + 1) n' in
  loop 0 n.

Definition elemIndices `{Monad m} {a : eqType} (x : a) : Pipe a nat m r :=
  findIndices (eq_op x).

Definition scan `{Monad m} `(step : x -> a -> x) (begin : x) `(done : x -> b) :
  Pipe a b m r :=
  let fix loop x n :=
    if n isn't S n' then Pure d else
    yield (done x) ;;
    a <-- await ;;
    let x' := step x a in
    loop x' n' in
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

Definition fold `{Monad m} `(step : x -> a -> x) (begin : x) `(done : x -> b)
  (p0 : Producer a m unit) : m b :=
  let fix loop p x := match p with
    | Request v  _  => False_rect _ v
    | Respond a  fu => loop (fu tt) (step x a)
    | M _     g  h  => h >>= fun p' => loop (g p') x
    | Pure    _     => return_ (done x)
    end in
  loop p0 begin.

Definition fold' `{Monad m} `(step : x -> a -> x) (begin : x) `(done : x -> b)
  (p0 : Producer a m r) : m (b * r)%type :=
  let fix loop p x := match p with
    | Request v  _  => False_rect _ v
    | Respond a  fu => loop (fu tt) (step x a)
    | M _     g  h  => h >>= fun p' => loop (g p') x
    | Pure    r     => return_ (done x, r)
    end in
  loop p0 begin.

Definition foldM `{Monad m}
  `(step : x -> a -> m x) (begin : m x) `(done : x -> m b)
  (p0 : Producer a m unit) : m b :=
  let fix loop p x := match p with
    | Request v  _  => False_rect _ v
    | Respond a  fu =>
          x' <-- step x a ;;
          loop (fu tt) x'
    | M _     g  h  => h >>= fun p' => loop (g p') x
    | Pure    _     => done x
    end in
  x0 <-- begin ;;
  loop p0 x0.

Definition foldM' `{Monad m}
  `(step : x -> a -> m x) (begin : m x) `(done : x -> m b)
  (p0 : Producer a m r) : m (b * r)%type :=
  let fix loop p x := match p with
    | Request v  _  => False_rect _ v
    | Respond a  fu =>
          x' <-- step x a ;;
          loop (fu tt) x'
    | M _     g  h  => h >>= fun p' => loop (g p') x
    | Pure    r     =>
          b <-- done x ;;
          return_ (b, r)
    end in
  x0 <-- begin ;;
  loop p0 x0.

Definition null `{Monad m} `(p : Producer a m unit) : m bool :=
  x <-- next p ;;
  return_ $ match x with
    | Left  _ => true
    | Right _ => false
    end.

Definition all `{Monad m} `(p : a -> bool) (p0 : Producer a m unit) : m bool :=
  null $ p0 >-> (filter (fun a => ~~ (p a)) >> return_ tt).

Definition any `{Monad m} `(p : a -> bool) (p0 : Producer a m unit) : m bool :=
  fmap negb $ null $ p0 >-> (filter p >> return_ tt).

Definition and `{Monad m} : Producer bool m unit -> m bool := all id.

Definition or `{Monad m} : Producer bool m unit -> m bool := any id.

Definition elem `{Monad m} {a : eqType} (x : a) : Producer a m unit -> m bool :=
  any (eq_op x).

Definition notElem `{Monad m} {a : eqType} (x : a) :
  Producer a m unit -> m bool :=
  all (negb \o eq_op x).

Definition head `{Monad m} `(p : Producer a m unit) : m (Maybe a) :=
  x <-- next p ;;
  return_ $ match x with
    | Left   _     => Nothing
    | Right (a, _) => Just a
    end.

Definition find `{Monad m} `(p : a -> bool) (p0 : Producer a m unit) :
  m (Maybe a) :=
  head (p0 >-> (filter p >> return_ tt)).

Definition findIndex `{Monad m} `(p : a -> bool) (p0 : Producer a m unit) :
  m (Maybe nat) :=
  head (p0 >-> (findIndices p >> return_ tt)).

Definition index `{Monad m} (n : nat) `(p : Producer a m unit) : m (Maybe a) :=
  head (p >-> (drop n >> return_ tt)).

Definition last `{Monad m} `(p0 : Producer a m unit) : m (Maybe a) :=
  let fix loop z p n : m (Maybe a) :=
    if n isn't S n' then return_ Nothing else
    x <-- next p ;;
    match x with
    | Left   _       => return_ (Just z)
    | Right (a', p') => loop a' p' n'
    end in
  x <-- next p0 ;;
  match x with
  | Left   _      => return_ Nothing
  | Right (a, p') => loop a p' n
  end.

Definition length `{Monad m} {a} : Producer a m unit -> m nat :=
  fold (fun n _ => n + 1) 0 id.

Definition maximum `{Monad m} : Producer nat m unit -> m (Maybe nat) :=
  let step x z := Just (match x with
    | Nothing => z
    | Just a' => max z a'
    end) in
  fold step Nothing id.

Definition minimum `{Monad m} : Producer nat m unit -> m (Maybe nat) :=
  let step x z := Just (match x with
    | Nothing => z
    | Just a' => min z a'
    end) in
  fold step Nothing id.

Definition sum `{Monad m} : Producer nat m unit -> m nat :=
  fold plus 0 id.

Definition product `{Monad m} : Producer nat m unit -> m nat :=
  fold mult 1 id.

Fixpoint toList `(p : Producer a id unit) : seq a :=
  if n isn't S n' then [::] else
  match p with
  | Request v _  => False_rect _ v
  | Respond a fu => a :: toList (fu tt)
  | M _     g h  => h >>= (toList \o g)
  | Pure    _    => [::]
  end.

(* This is the version of toListM defined by the pipes library, but it is not
   very amenable to proof. *)

Definition toListM_fold `{Monad m} {a} : Producer a m unit -> m (seq a) :=
  let step x a := x \o (cons a) in
  let begin    := id in
  let done x   := x [::] in
  fold step begin done.

Fixpoint toListM `{Monad m} `(p : Producer a m unit) : m (seq a) :=
  match p with
  | Request v _  => False_rect _ v
  | Respond x fu => cons x <$> toListM (fu tt)
  | M _     f t  => t >>= (toListM \o f)
  | Pure    _    => pure [::]
  end.

(*
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
    dn v = False_rect _ v

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
