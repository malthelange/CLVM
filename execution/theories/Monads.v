Require Import Basics.
Require Import List.
Import ListNotations.

Definition pure {A} : A -> option A := fun x => Some x.

Definition option_bind {A B : Type} (v : option A) (f : A -> option B) : option B :=
  match v with
  | Some val => f val
  | None => None
  end.
Class Monad (m : Type -> Type) : Type :=
build_monad {
  ret : forall {t}, t -> m t;
  bind : forall {t u}, m t -> (t -> m u) -> m u
}.

Global Instance option_monad : Monad option :=
  {| ret _ t := Some t;
     bind _ _ v f := match v with
                 | Some val => f val
                 | None => None
                 end |}.

Notation "c >>= f" := (bind c f) (at level 50, left associativity).
Notation "f =<< c" := (bind c f) (at level 51, right associativity).


Definition liftM {A B} (f : A -> B) (x : option A) : option B :=
  x >>= (compose pure  f).

Definition liftM2 {A B C} (f : A -> B -> C) (x : option A) (y : option B) : option C :=
 x >>= (fun x' => y >>=  compose pure (f x')).

Definition liftM3 {A B C D} (f : A -> B -> C -> D) (x : option A) (y : option B) (z : option C) : option D :=
 x >>= (fun x' => y >>= fun y' => z >>=  compose pure (f x' y')).

Fixpoint mapM {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
    | nil => Some nil
    | x :: xs => liftM2 (fun x' xs' => x' :: xs') (f x) (mapM f xs)
  end.

Notation "'do' x <- c1 ; c2" :=
  (bind c1 (fun x => c2))
    (at level 60, c1 at next level, right associativity).

Notation "'do' ' pat <- c1 ; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
    (at level 60, pat pattern, c1 at next level, right associativity).

Notation "'do' e1 ; e2" := (do _ <- e1 ; e2)
  (at level 60, right associativity).

Fixpoint sequence {A} (l : list (option A)) : option (list A) :=
  match l with
    | nil => Some nil
    | x :: xs => liftM2 (fun x' xs' => x' :: xs') x (sequence xs)
  end.

Class MonadLaws {m : Type -> Type} (mon : Monad m) :=
build_monad_laws {
  bind_of_return :
    forall (T : Type) (t : T) (U : Type) (f : T -> m U),
      (ret t >>= f) = f t;
  return_of_bind :
    forall (T : Type) (t : m T),
      (t >>= @ret m mon T) = t;
  bind_assoc :
    forall (T U V : Type) (t : m T) (f : T -> m U) (g : U -> m V),
      (t >>= f) >>= g = t >>= (fun t => f t >>= g);
}.

Class MonadTrans (m : Type -> Type) (mt : Type -> Type) : Type :=
  { lift : forall {t}, mt t -> m t }.



Global Instance option_monad_laws : MonadLaws option_monad.
Proof.
  constructor.
  - auto.
  - intros; cbn.
    destruct t; auto.
  - intros; cbn.
    destruct t; auto.
Qed.

