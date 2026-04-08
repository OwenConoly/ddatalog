From Stdlib Require Import String List.
Import ListNotations.

(* Define the result type *)
Inductive result (A : Type) :=
| Success (value : A)
| Failure (error : string).

Arguments Success {A} _.
Arguments Failure {A} _.

(* Monadic bind *)
Definition bind {A B : Type} (r : result A) (f : A -> result B) : result B :=
  match r with
  | Success v => f v
  | Failure e => Failure e
  end.

(* Infix notation for bind *)
Infix ">>=" := bind (at level 50, left associativity).

(* Map function *)
Definition fmap {A B : Type} (r : result A) (f : A -> B) : result B :=
  match r with
  | Success v => Success (f v)
  | Failure e => Failure e
  end.

Infix "<$>" := fmap (at level 50, left associativity).

(* Map a fallible function over a list, collecting results *)
Definition result_map {A B : Type} (f : A -> result B) (l : list A) : result (list B) :=
  fold_left (fun acc x =>
    acc >>= fun xs =>
    f x >>= fun y =>
    Success (xs ++ [y])
  ) l (Success []).

(* Fold with a fallible function *)
Definition result_fold {A B : Type} (f : B -> A -> result B) (init : result B) (l : list A) : result B :=
  fold_left (fun acc x => acc >>= fun b => f b x) l init.

Notation "'let*' x ':=' e 'in' f" := (e >>= fun x => f)
  (at level 60, x pattern, right associativity).