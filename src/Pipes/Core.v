Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Identity.
Require Import P.Pipes.Internal.

Generalizable All Variables.

Fixpoint runEffect `{Monad m} `(p : Proxy False unit unit False m r) : m r :=
  match p with
  | Request v f => False_rect _ v
  | Respond v f => False_rect _ v
  | M _     f t => t >>= (runEffect \o f)
  | Pure    r   => pure r
  end.

Definition respond {x' x a' a m} (z : a) : Proxy x' x a' a m a' :=
  Respond z Pure.

Definition forP `{Monad m} {x' x a' b' b c' c} (p0 : Proxy x' x b' b m a')
  (fb : b -> Proxy x' x c' c m b') : Proxy x' x c' c m a' :=
  let fix go p := match p with
    | Request x' fx  => Request x' (go \o fx)
    | Respond b  fb' => fb b >>= (go \o fb')
    | M _     f  t   => M (go \o f) t
    | Pure       a   => Pure a
    end in
  go p0.

Notation "x //> y" := (forP x y) (at level 60).

Notation "f />/ g" := (fun a => f a //> g) (at level 60).

Definition request {x' x a' a m} (z : x') : Proxy x' x a' a m x :=
  Request z Pure.

Definition rofP `{Monad m} {y' y a' a b' b c} (fb' : b' -> Proxy a' a y' y m b)
  (p0 : Proxy b' b y' y m c) : Proxy a' a y' y m c :=
  let fix go p := match p with
    | Request b' fb  => fb' b' >>= (go \o fb)
    | Respond x  fx' => Respond x (go \o fx')
    | M _     f  t   => M (go \o f) t
    | Pure       a   => Pure a
    end in
  go p0.

Notation "x >\\ y" := (rofP x y) (at level 60).

Notation "f \>\ g" := (fun a => f >\\ g a) (at level 60).

(* Very strangly, if the order of [fb] and [p0] is reversed, then the right
   identity law for the push category will fail to complete with a universe
   inconsistency. *)
Fixpoint pushR `{Monad m} {a' a b' b c' c r} (fb : b -> Proxy b' b c' c m r)
  (p0 : Proxy a' a b' b m r) {struct p0} : Proxy a' a c' c m r :=
  match p0 with
  | Request a' fa  => Request a' (pushR fb \o fa)
  | Respond b  fb' =>
      let fix go' p := match p with
        | Request b' fb  => pushR fb (fb' b')
        | Respond c  fc' => Respond c (go' \o fc')
        | M _     f  t   => M (go' \o f) t
        | Pure       a   => Pure a
        end in
      go' (fb b)
  | M _     f  t   => M (pushR fb \o f) t
  | Pure       a   => Pure a
  end.

Notation "x >>~ y" := (pushR y x) (at level 60).

Notation "f >~> g" := (fun a => f a >>~ g) (at level 60).

Fixpoint pullR `{Monad m} {a' a b' b c' c r} (fb' : b' -> Proxy a' a b' b m r)
  (p0 : Proxy b' b c' c m r) {struct p0} : Proxy a' a c' c m r :=
  match p0 with
  | Request b' fb  =>
      let fix go' p := match p with
        | Request a' fa  => Request a' (go' \o fa)
        | Respond b  fb' => pullR fb' (fb b)
        | M _     f  t   => M (go' \o f) t
        | Pure       a   => Pure a
        end in
      go' (fb' b')
  | Respond c  fc' => Respond c (pullR fb' \o fc')
  | M _     f  t   => M (pullR fb' \o f) t
  | Pure       a   => Pure a
  end.

Notation "x +>> y" := (pullR x y) (at level 60).

Notation "f >+> g" := (fun a => f +>> g a) (at level 60).

Definition reflect `{Monad m} `(p : Proxy a' a b' b m r) :
  Proxy b b' a a' m r :=
  let fix go p := match p with
    | Request a' fa  => Respond a' (go \o fa)
    | Respond b  fb' => Request b  (go \o fb')
    | M _     g  h   => M (go \o g) h
    | Pure    r      => Pure r
    end in
  go p.

Definition Effect               := Proxy False unit unit False.
Definition Producer             := Proxy False unit unit.
Definition Pipe (a b : Type)    := Proxy unit a unit b.
Definition Consumer (a : Type)  := Proxy unit a unit False.
Definition Client (a' a : Type) := Proxy a' a unit False.
Definition Server               := Proxy False unit.

Definition Effect' m r          := forall x' x y' y, Proxy x' x y' y m r.
Definition Producer' b m r      := forall x' x, Proxy x' x unit b m r.
Definition Consumer' a m r      := forall y' y, Proxy unit a y' y m r.
Definition Client' a' a m r     := forall y' y, Proxy a' a y' y m r.
Definition Server' b' b m r     := forall x' x, Proxy x' x b' b m r.

Notation "f \<\ g" := (g />/ f) (at level 60).
Notation "f /</ g" := (g \>\ f) (at level 60).
Notation "f <~< g" := (g >~> f) (at level 60).
Notation "f <+< g" := (g >+> f) (at level 60).
Notation "f <// x" := (x //> f) (at level 60).
Notation "x //< f" := (f >\\ x) (at level 60).
Notation "f ~<< x" := (x >>~ f) (at level 60).
Notation "x <<+ f" := (f +>> x) (at level 60).

(* These definitions should be moved, and the laws that use them. *)

Definition yield {a x' x m} (z : a) : Proxy x' x unit a m unit :=
  let go : Producer' a m unit := fun _ _ => respond z in @go x' x.

(* Notation "f ~> g" := (f />/ g) (at level 70). *)
(* Notation "f <~ g" := (f ~> g) (at level 70). *)

Definition await {a y' y m} (z : a) : Proxy unit a y' y m a :=
  let go : Consumer' a m a := fun _ _ => request tt in @go y' y.

Notation "x >~ y" := ((fun _ : unit => x) >\\ y) (at level 70).
Notation "x ~< y" := (y >~ x) (at level 70).

Definition connect `{Monad m} `(p1 : Proxy a' a unit b m r)
  `(p2 : Proxy unit b c' c m r) : Proxy a' a c' c m r :=
  (fun _ : unit => p1) +>> p2.

Notation "x >-> y" := (connect x y) (at level 60).
Notation "x <-< y" := (y >-> x) (at level 60).

(****************************************************************************
 ****************************************************************************
 **                                                                        **
 ** Proofs of the pipes categories and laws                                **
 **                                                                        **
 ****************************************************************************
 ****************************************************************************)

Module PipesLawsCore.

Include PipesLawsInternal.

Require Import Hask.Control.Category.
Require Import FunctionalExtensionality.

(****************************************************************************
 *
 * Respond Category
 *)

Section Respond.

Theorem respond_distrib `{MonadLaws m} :
  forall (x' x a' a b' b c' c r : Type)
         (f : a  -> Proxy x' x b' b m a')
         (g : a' -> Proxy x' x b' b m r)
         (h : b  -> Proxy x' x c' c m b'),
  (f >=> g) />/ h =1 (f />/ h) >=> (g />/ h).
Proof.
  move=> ? ? ? ? ? ? ? ? ? f ? ? x.
  rewrite /kleisli_compose.
  elim: (f x) => // [? ? IHx|? ? IHx|? ? IHx].
  - rewrite /bind /=.
    f_equal.
    extensionality a1.
    exact: IHx.
  - apply functional_extensionality in IHx.
    by rewrite /= /funcomp IHx /bind /funcomp
               -join_fmap_fmap_x fmap_comp_x
               -join_fmap_join_x fmap_comp_x.
  - move=> m0.
    rewrite /bind /=.
    f_equal.
    extensionality y.
    exact: IHx.
Qed.

Program Instance Respond_Category {x' x} `{MonadLaws m} : Category := {
  ob     := Type * Type;
  hom    := fun A B => snd A -> Proxy x' x (fst B) (snd B) m (fst A);
  c_id   := fun A => @respond x' x (fst A) (snd A) m;
  c_comp := fun _ _ _ f g => g />/ f
}.
Obligation 1. (* Right identity *)
  extensionality z.
  exact: join_fmap_pure_x.
Qed.
Obligation 2. (* Left identity *)
  extensionality z.
  move: (f z).
  by reduce_proxy IHx (rewrite /= /bind /funcomp /=).
Qed.
Obligation 3. (* Associativity *)
  extensionality z.
  elim: (h z) => // [? ? IHx|? ? IHx|? ? IHx].
  - rewrite /=.
    f_equal.
    extensionality a1.
    exact: IHx.
  - apply functional_extensionality in IHx.
    by rewrite /= /funcomp -IHx respond_distrib.
  - move=> m0.
    rewrite /=.
    f_equal.
    rewrite /funcomp.
    extensionality y.
    exact: IHx.
Qed.

Corollary respond_zero `{MonadLaws m} : forall `(f : c -> Proxy a' a b' b m r),
  pure />/ f =1 @pure _ Proxy_Applicative r.
Proof. by []. Qed.

End Respond.

(****************************************************************************
 *
 * Request Category
 *)

Section Request.

Theorem request_distrib `{MonadLaws m} :
  forall (y' y a' a b' b c' c r : Type)
         (f : c -> Proxy b' b y' y m c')
         (g : c'  -> Proxy b' b y' y m r)
         (h : b' -> Proxy a' a y' y m b),
  h \>\ (f >=> g) =1 (h \>\ f) >=> (h \>\ g).
Proof.
  move=> ? ? ? ? ? ? ? ? ? f ? ? x.
  rewrite /kleisli_compose.
  elim: (f x) => // [? ? IHx|? ? IHx|? ? IHx].
  - apply functional_extensionality in IHx.
    by rewrite /= /funcomp IHx /bind /funcomp
               -join_fmap_fmap_x fmap_comp_x
               -join_fmap_join_x fmap_comp_x.
  - rewrite /bind /=.
    f_equal.
    extensionality a1.
    exact: IHx.
  - move=> m0.
    rewrite /bind /=.
    f_equal.
    extensionality y.
    exact: IHx.
Qed.

Program Instance Request_Category {x' x} `{MonadLaws m} : Category := {
  ob     := Type * Type;
  hom    := fun A B => fst A -> Proxy (fst B) (snd B) x' x m (snd A);
  c_id   := fun A => @request (fst A) (snd A) x' x m;
  c_comp := fun _ _ _ f g => f \>\ g
}.
Obligation 1. (* Right identity *)
  extensionality z.
  move: (f z).
  by reduce_proxy IHx (rewrite /= /bind /funcomp /=).
Qed.
Obligation 2. (* Left identity *)
  extensionality z.
  move: (f z).
  by reduce_proxy IHx (rewrite /= /bind /funcomp /=).
Qed.
Obligation 3. (* Associativity *)
  extensionality z.
  elim: (h z) => // [y p IHx|? ? IHx|? ? IHx].
  - apply functional_extensionality in IHx.
    by rewrite /= /funcomp -IHx request_distrib.
  - rewrite /=.
    f_equal.
    extensionality a1.
    exact: IHx.
  - move=> m0.
    rewrite /=.
    f_equal.
    rewrite /funcomp.
    extensionality y.
    exact: IHx.
Qed.

Corollary request_zero `{MonadLaws m} : forall `(f : c -> Proxy a' a b' b m r),
  f \>\ pure =1 @pure _ Proxy_Applicative r.
Proof. by []. Qed.

End Request.

(****************************************************************************
 *
 * Push Category
 *)

Tactic Notation "reduce_over" constr(f) ident(g) ident(y) ident(IHx) :=
  move=> ? ? ? ? ? ? ? ? g ?;
  rewrite /= /funcomp;
  congr (f _ _);
  extensionality y;
  move: (g y);
  by reduce_proxy IHx simpl.

Section Push.

Definition push `{Monad m} {a' a r} {n : nat} {default : r} :
  a -> Proxy a' a a' a m r :=
  let fix go n x :=
    if n isn't S n' then Pure default else
    (Respond ^~ (Request ^~ @go n')) x
  in go n.

Lemma push_request `{Monad m} :
  forall `(f : b -> Proxy b' b c' c m r)
         `(g : a -> Proxy a' a b' b m r) x,
  Request x g >>~ f = Request x (g >~> f).
Proof. reduce_over @Request g y IHx. Qed.

Lemma push_m `{Monad m} :
  forall `(f : b -> Proxy b' b c' c m r)
         `(g : x -> Proxy a' a b' b m r) (h : m x),
  M g h >>~ f = M (g >~> f) h.
Proof. move=> x; reduce_over @M g y IHx. Qed.

Variable n : nat.
Variable r : Type.
Variable default : r.

Hypothesis Hn : n > 0.
Hypothesis Hpush :
  forall `{Monad m} a' a n', @push m _ a' a r n' default =
                             @push m _ a' a r n'.+1 default.

Program Instance Push_Category `{MonadLaws m} : Category := {
  ob     := Type * Type;
  hom    := fun A B => snd B -> Proxy (fst B) (snd B) (fst A) (snd A) m r;
  c_id   := fun A => @push m _ (fst A) (snd A) r n default;
  c_comp := fun _ _ _ f g => f >~> g
}.
Obligation 1. (* Right identity *)
  extensionality z.
  move: (f z).
  reduce_proxy IHx simpl.
  move: Hn.
  case E: n => // [n'] _.
  congr (Respond _ _).
  rewrite /funcomp -/push Hpush.
  rewrite E in IHx.
  move/functional_extensionality in IHx.
  exact: IHx.
Qed.
Obligation 2. (* Left identity *)
  extensionality z.
  rewrite /push.
  move: Hn.
  case E: n => //= [n'] _.
  rewrite -/push.
  move: (f z).
  reduce_proxy IHx simpl.
  congr (Request _ _).
  rewrite /flip /funcomp Hpush.
  extensionality w.
  by rewrite -IHx.
Qed.
Obligation 3. (* Associativity *)
  simpl in *.
  extensionality z.
  move: g h.
  elim: (f z) => // [? ? IHx|b fb' IHx|? ? IHx] g h.
  - rewrite 3!push_request.
    congr (Request _ _).
    extensionality w.
    exact: IHx.
  - rewrite /=.
    move: h.
    move: (g b).
    reduce_proxy IHy (rewrite /= /flip /funcomp /=) => h.
    + exact: IHx.
    + move: (h _).
      reduce_proxy IHz (rewrite /= /flip /funcomp /=).
      exact: IHy.
  - move=> m0.
    rewrite 3!push_m.
    congr (M _ _).
    extensionality w.
    exact: IHx.
Qed.

End Push.

(****************************************************************************
 *
 * Pull Category
 *)

Section Pull.

Lemma pull_respond `{Monad m} :
  forall `(f : b' -> Proxy a' a b' b m r)
         `(g : c' -> Proxy b' b c' c m r) x,
  f +>> Respond x g = Respond x (f >+> g).
Proof. reduce_over @Respond g y IHx. Qed.

Lemma pull_m `{Monad m} :
  forall x `(f : b' -> Proxy a' a b' b m r)
         `(g : x -> Proxy b' b c' c m r) (h : m x),
  f +>> M g h = M (f >+> g) h.
Proof. move=> x; reduce_over @M g y IHx. Qed.

Definition pull `{Monad m} {a' a r} {n : nat} {default : r} :
  a' -> Proxy a' a a' a m r :=
  let fix go n x :=
    if n isn't S n' then Pure default else
    (Request ^~ (Respond ^~ @go n')) x
  in go n.

Variable n : nat.
Variable r : Type.
Variable default : r.

Definition cat `{Monad m} {a} : Pipe a a m r :=
  pull (n:=n) (default:=default) tt.

Definition map `{Monad m} `(f : a -> b) : Pipe a b m r := forP cat (yield \o f).

Hypothesis Hn : n > 0.
Hypothesis Hpull :
  forall n' `{Monad m} a' a, @pull m _ a' a r n' default =
                             @pull m _ a' a r n'.+1 default.

Program Instance Pull_Category `{MonadLaws m} : Category := {
  ob     := Type * Type;
  hom    := fun A B => fst A -> Proxy (fst B) (snd B) (fst A) (snd A) m r;
  c_id   := fun A => @pull m _ (fst A) (snd A) r n default;
  c_comp := fun _ _ _ f g => f >+> g
}.
Obligation 1. (* Right identity *)
  extensionality z.
  rewrite /push.
  move: Hn.
  case E: n => //= [n'] _.
  rewrite -/push.
  move: (f z).
  reduce_proxy IHx simpl.
  congr (Respond _ _).
  rewrite /flip /funcomp Hpull.
  extensionality w.
  by rewrite -IHx.
Qed.
Obligation 2. (* Left identity *)
  extensionality z.
  move: (f z).
  reduce_proxy IHx simpl.
  move: Hn.
  case E: n => // [n'] _.
  congr (Request _ _).
  rewrite /funcomp -/pull Hpull.
  rewrite E in IHx.
  move/functional_extensionality in IHx.
  exact: IHx.
Qed.
Obligation 3. (* Associativity *)
  simpl in *.
  extensionality z.
  move: f g.
  elim: (h z) => // [a' fa IHx|? ? IHx|? ? IHx] f g.
  - rewrite /=.
    move: f.
    move: (g a').
    reduce_proxy IHy (rewrite /= /flip /funcomp /=) => f.
    + move: (f _).
      reduce_proxy IHz (rewrite /= /flip /funcomp /=).
      exact: IHy.
    + exact: IHx.
  - rewrite 3!pull_respond.
    congr (Respond _ _).
    extensionality w.
    exact: IHx.
  - move=> m0.
    rewrite 3!pull_m.
    congr (M _ _).
    extensionality w.
    exact: IHx.
Qed.

Theorem push_pull_assoc `{MonadLaws m} :
  forall `(f : b' -> Proxy a' a b' b m r)
         `(g : a  -> Proxy b' b c' c m r)
          (h : c  -> Proxy c' c b' b m r),
  (f >+> g) >~> h =1 f >+> (g >~> h).
Proof.
  move=> ? ? ? ? f ? ? g h a.
  move: f h.
  elim: (g a) => // [a' fa IHx|b fb' IHx|? ? IHx] => f h.
  - rewrite push_request.
    rewrite /=.
    move: h.
    move: (f a').
    reduce_proxy IHy (rewrite /= /flip /funcomp /=) => h.
    exact: IHx.
  - rewrite pull_respond.
    rewrite /=.
    move: f.
    move: (h b).
    reduce_proxy IHy (rewrite /= /flip /funcomp /=) => f.
    exact: IHx.
  - move=> m0.
    rewrite pull_m push_m push_m pull_m.
    congr (M _ f).
    extensionality w.
    exact: IHx.
Qed.

Theorem map_id : forall a, map (@id a) = cat.
Proof.
  move=> a.
  rewrite /map /cat /yield /respond /forP.
  move: (pull tt).
  by reduce_proxy IHx (rewrite /bind /funcomp /=).
Qed.

Theorem map_compose `{MonadLaws m} : forall `(f : a -> b) `(g : b -> c),
    map (g \o f) = map f >-> map g.
Proof.
  move=> a b f c g.
  rewrite /map /cat /yield /funcomp.
  move: (pull tt).
  reduce_proxy IHx (rewrite /= /funcomp);
  try move/functional_extensionality in IHx;
  move: Hn;
  case E: n => //= [n'] _.
  - rewrite E in IHx.
    rewrite IHx.
    congr (Request _ _).
    rewrite IHx /bind /funcomp /= /funcomp /connect /=.
    congr (Respond _ _).
    rewrite /funcomp /=.
    extensionality t.
    f_equal.
    extensionality u.
    by destruct t, u.
  - destruct t.
    by rewrite E -Hpull.
  - move=> m0.
    rewrite E in IHx.
    rewrite IHx.
    by congr (M _ _).
Qed.

End Pull.

(****************************************************************************
 *
 * Reflection (Duals)
 *)

Section Duals.

Variables a' a b' b r : Type.
Variables m : Type -> Type.
Context `{MonadLaws m}.

Theorem request_id : reflect \o request =1 @respond a' a b' b m.
Proof. move=> x; by congr (Respond _ _). Qed.

Theorem reflect_distrib :
  forall (f : a -> Proxy a' a b' b m r)
         (g : r -> Proxy a' a b' b m r) (x : a),
    reflect (f x >>= g) = reflect (f x) >>= (reflect \o g).
Proof.
  move=> f g x.
  move: (f x).
  by reduce_proxy IHx (rewrite /bind /=).
Qed.

Theorem request_comp :
  forall (f : a -> Proxy a' a b' b m r)
         (g : a -> Proxy a  r b' b m r),
    reflect \o (f \>\ g) =1 (reflect \o g) />/ (reflect \o f).
Proof.
  move=> f g x.
  rewrite /=.
  move: (g x).
  reduce_proxy IHx simpl.
  move/functional_extensionality in IHx.
  by rewrite /funcomp -IHx reflect_distrib.
Qed.

Theorem respond_id : reflect \o respond =1 @request a' a b' b m.
Proof. move=> x; by congr (Request _ _). Qed.

Theorem respond_comp :
  forall (f : a -> Proxy a' a b' b m r)
         (g : b -> Proxy a' a b' b m b'),
    reflect \o (f />/ g) =1 (reflect \o g) \>\ (reflect \o f).
Proof.
  move=> f g x.
  rewrite /=.
  move: (f x).
  reduce_proxy IHx simpl.
  move/functional_extensionality in IHx.
  (* jww (2015-06-09): We should be able to use [reflect_distrib] here, but
     the types are not general enough, which means that the types of some of
     these theorems are probably incorrect. *)
  rewrite /funcomp -IHx.
  move: (g _).
  by reduce_proxy IHy (rewrite /bind /=).
Qed.

Corollary distributivity :
  forall (f : a -> Proxy a' a b' b m r)
         (g : r -> Proxy a' a b' b m r),
    reflect \o (f >=[Proxy_Monad]=> g) =1 (reflect \o f) >=> (reflect \o g).
Proof. exact: reflect_distrib. Qed.

Theorem zero_law : @reflect m _ a' a b' b r \o pure =1 pure.
Proof. by []. Qed.

Theorem involution : @reflect m _ a' a b' b r \o reflect =1 id.
Proof. by reduce_proxy IHx simpl. Qed.

End Duals.

End PipesLawsCore.