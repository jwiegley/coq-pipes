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

Definition push {a' a m r} {n : nat} {default : r} :
  a -> Proxy a' a a' a m r :=
  let fix go n x :=
    if n isn't S n' then Pure default else
    (Respond ^~ (Request ^~ @go n')) x
  in go n.

(* Very strangly, if the order of [fb] and [p0] is reversed, then the right
   identity law for the push category will fail to complete with a universe
   inconsistency. *)
Fixpoint pushR {a' a b' b c' c m r} (fb : b -> Proxy b' b c' c m r)
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

Definition pull {a' a m r} {n : nat} {default : r} :
  a' -> Proxy a' a a' a m r :=
  let fix go n x :=
    if n isn't S n' then Pure default else
    (Request ^~ (Respond ^~ @go n')) x
  in go n.

Fixpoint pullR {a' a b' b c' c m r} (fb' : b' -> Proxy a' a b' b m r)
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

Notation "f \<\ g" := (g />/ f) (at level 60, only parsing).
Notation "f /</ g" := (g \>\ f) (at level 60, only parsing).
Notation "f <~< g" := (g >~> f) (at level 60, only parsing).
Notation "f <+< g" := (g >+> f) (at level 60, only parsing).
Notation "f <// x" := (x //> f) (at level 60, only parsing).
Notation "x //< f" := (f >\\ x) (at level 60, only parsing).
Notation "f ~<< x" := (x >>~ f) (at level 60, only parsing).
Notation "x <<+ f" := (f +>> x) (at level 60, only parsing).

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

Ltac applying_monad_laws IHx X :=
  rewrite ?/kleisli_compose;
  move: X;
  reduce_proxy IHx
    (first [ apply functional_extensionality in IHx;
             by rewrite /= /funcomp IHx /bind /funcomp
               -join_fmap_fmap_x fmap_comp_x
               -join_fmap_join_x fmap_comp_x
           | rewrite /bind /= ]).

Ltac applying_theorem IHx X H :=
  rewrite ?/kleisli_compose;
  move: X;
  reduce_proxy IHx
    (first [ apply functional_extensionality in IHx;
             by rewrite /= /funcomp -IHx H
           | rewrite /= ]).

Ltac mere_extensionality IHx x f :=
  extensionality x;
  move: (f x);
  reduce_proxy IHx (rewrite /= /bind /=).

Section Respond.

Theorem respond_distrib `{MonadLaws m} :
  forall (x' x a' a b' b c' c r : Type)
         (f : a  -> Proxy x' x b' b m a')
         (g : a' -> Proxy x' x b' b m r)
         (h : b  -> Proxy x' x c' c m b'),
  (f >=> g) />/ h =1 (f />/ h) >=> (g />/ h).
Proof.
  move=> ? ? ? ? ? ? ? ? ? f ? ? x.
  by applying_monad_laws IHx (f x).
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
  by mere_extensionality IHx z f.
Qed.
Obligation 3. (* Associativity *)
  extensionality z.
  by applying_theorem IHx (h z) respond_distrib.
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
  by applying_monad_laws IHx (f x).
Qed.

Program Instance Request_Category {x' x} `{MonadLaws m} : Category := {
  ob     := Type * Type;
  hom    := fun A B => fst A -> Proxy (fst B) (snd B) x' x m (snd A);
  c_id   := fun A => @request (fst A) (snd A) x' x m;
  c_comp := fun _ _ _ f g => f \>\ g
}.
Obligation 1. (* Right identity *)
  by mere_extensionality IHx z f.
Qed.
Obligation 2. (* Left identity *)
  by mere_extensionality IHx z f.
Qed.
Obligation 3. (* Associativity *)
  extensionality z.
  by applying_theorem IHx (h z) request_distrib.
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
  congr (f _ _);
  by mere_extensionality IHx y g.

Module Compromise.

Variable n : nat.
Hypothesis Hn : n > 0.

Variable r : Type.
Variable d : r.

Hypothesis Hpush : forall m a' a n d,
  @push a' a m r n d = @push a' a m r n.+1 d.

Hypothesis Hpull : forall m a' a n d,
  @pull a' a m r n d = @pull a' a m r n.+1 d.

Global Ltac assume_infinity :=
  move: Hn;
  case E: n => // [n'] _.

End Compromise.

Module Push.

Lemma push_request `{Monad m} :
  forall `(f : b -> Proxy b' b c' c m r)
         `(g : a -> Proxy a' a b' b m r) x,
  Request x g >>~ f = Request x (g >~> f).
Proof. by reduce_over @Request g y IHx. Qed.

Lemma push_m `{Monad m} :
  forall `(f : b -> Proxy b' b c' c m r)
         `(g : x -> Proxy a' a b' b m r) (h : m x),
  M g h >>~ f = M (g >~> f) h.
Proof. by move=> x; reduce_over @M g y IHx. Qed.

Include Compromise.

Program Instance Push_Category `{MonadLaws m} : Category := {
  ob     := Type * Type;
  hom    := fun A B => snd B -> Proxy (fst B) (snd B) (fst A) (snd A) m r;
  c_id   := fun A => @push (fst A) (snd A) m r n d;
  c_comp := fun _ _ _ f g => f >~> g
}.
Obligation 1. (* Right identity *)
  mere_extensionality IHx z f.
  assume_infinity.
  congr (Respond _ _).
  rewrite -/push Hpush.
  rewrite E in IHx.
  move/functional_extensionality in IHx.
  exact: IHx.
Qed.
Obligation 2. (* Left identity *)
  extensionality z.
  assume_infinity => /=.
  move: (f z).
  reduce_proxy IHx simpl.
  congr (Request _ _).
  rewrite /flip Hpush.
  extensionality w.
  by rewrite -IHx.
Qed.
Obligation 3. (* Associativity *)
  extensionality z.
  move: (f z) g h.
  reduce_proxy IHx
    (move=> g h;
     first [ rewrite 3!push_request;
             congr (Request _ _)
           | rewrite 3!push_m;
             congr (M _ _)
           | rewrite /= ]).
  move: (g _) h.
  reduce_proxy IHy (rewrite /= /flip /=) => h.
  - exact: IHx.
  - move: (h _).
    reduce_proxy IHz (rewrite /= /flip /=).
    exact: IHy.
Qed.

End Push.

(****************************************************************************
 *
 * Pull Category
 *)

Module Pull.

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

Include Push.

Program Instance Pull_Category `{MonadLaws m} : Category := {
  ob     := Type * Type;
  hom    := fun A B => fst A -> Proxy (fst B) (snd B) (fst A) (snd A) m r;
  c_id   := fun A => @pull (fst A) (snd A) m r n d;
  c_comp := fun _ _ _ f g => f >+> g
}.
Obligation 1. (* Right identity *)
  extensionality z.
  assume_infinity => /=.
  move: (f z).
  reduce_proxy IHx simpl.
  congr (Respond _ _).
  rewrite /flip Hpull.
  extensionality w.
  by rewrite -IHx.
Qed.
Obligation 2. (* Left identity *)
  extensionality z.
  move: (f z).
  reduce_proxy IHx simpl.
  assume_infinity.
  congr (Request _ _).
  rewrite -/pull Hpull.
  rewrite E in IHx.
  move/functional_extensionality in IHx.
  exact: IHx.
Qed.
Obligation 3. (* Associativity *)
  extensionality z.
  move: (h z) f g.
  reduce_proxy IHx
    (move=> f g;
     first [ rewrite 3!pull_request;
             congr (Respond _ _)
           | rewrite 3!push_m;
             congr (M _ _)
           | rewrite /= ]).
  rewrite /=.
  move: (g _) f.
  reduce_proxy IHy (rewrite /= /flip /=) => f.
  - move: (f _).
    reduce_proxy IHz (rewrite /= /flip /=).
    exact: IHy.
  - exact: IHx.
Qed.

Theorem push_pull_assoc `{MonadLaws m} :
  forall `(f : b' -> Proxy a' a b' b m r)
         `(g : a  -> Proxy b' b c' c m r)
          (h : c  -> Proxy c' c b' b m r),
  (f >+> g) >~> h =1 f >+> (g >~> h).
Proof.
  move=> ? ? ? ? f ? ? g h ?.
  move: (g _) f h.
  reduce_proxy IHx
    (move=> f h;
     try (rewrite pull_m push_m push_m pull_m;
          congr (M _ _))) => //.
  - rewrite push_request /=.
    move: (f _) h.
    reduce_proxy IHy simpl => h.
    exact: IHx.
  - rewrite pull_respond /=.
    move: (h _) f.
    reduce_proxy IHy simpl => f.
    exact: IHx.
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
  move=> f ? ?.
  move: (f _).
  by reduce_proxy IHx (rewrite /bind /=).
Qed.

Theorem request_comp :
  forall (f : a -> Proxy a' a b' b m r)
         (g : a -> Proxy a  r b' b m r),
    reflect \o (f \>\ g) =1 (reflect \o g) />/ (reflect \o f).
Proof.
  move=> ? g x /=.
  by applying_theorem IHx (g x) reflect_distrib.
Qed.

Theorem respond_id : reflect \o respond =1 @request a' a b' b m.
Proof. by move=> ?; congr (Request _ _). Qed.

Theorem respond_comp :
  forall (f : a -> Proxy a' a b' b m r)
         (g : b -> Proxy a' a b' b m b'),
    reflect \o (f />/ g) =1 (reflect \o g) \>\ (reflect \o f).
Proof.
  move=> f g ? /=.
  move: (f _).
  by reduce_proxy IHx
    (first [ move/functional_extensionality in IHx;
             rewrite /= /funcomp -IHx;
             (* jww (2015-06-09): We should be able to use [reflect_distrib]
                here, but the types are not general enough, which means the
                types of some of these theorems may be insufficient. *)
             move: (g _);
             reduce_proxy IHy (rewrite /bind /=)
           | rewrite /= ]).
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