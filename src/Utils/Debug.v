From Stdlib Require Import String List.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(* A debug result carries a trace of log messages alongside success/failure *)
Inductive debug (A : Type) :=
| DSuccess (trace : list string) (value : A)
| DFailure (trace : list string) (error : string).

Arguments DSuccess {A} _ _.
Arguments DFailure {A} _ _.

(* Extract the trace regardless of outcome *)
Definition get_trace {A : Type} (d : debug A) : list string :=
  match d with
  | DSuccess trace _ => trace
  | DFailure trace _  => trace
  end.

(* Monadic bind — threads the trace through both branches *)
Definition dbind {A B : Type} (d : debug A) (f : A -> debug B) : debug B :=
  match d with
  | DFailure trace e => DFailure trace e
  | DSuccess trace v =>
    match f v with
    | DSuccess trace' v' => DSuccess (trace ++ trace') v'
    | DFailure trace' e  => DFailure (trace ++ trace') e
    end
  end.

Infix ">>~" := dbind (at level 50, left associativity).

(* let* notation for readable monadic chains *)
Notation "'dlet*' x ':=' e 'in' f" := (e >>~ fun x => f)
  (at level 60, x pattern, right associativity).

(* Pure lift — no log messages *)
Definition dreturn {A : Type} (v : A) : debug A :=
  DSuccess [] v.

(* Log a message and continue with a value *)
Definition dlog {A : Type} (msg : string) (v : A) : debug A :=
  DSuccess [msg] v.

(* Log a message without producing a value *)
Definition dtrace (msg : string) : debug unit :=
  DSuccess [msg] tt.

(* Fail with a message, also recording it in the trace *)
Definition dfail {A : Type} (msg : string) : debug A :=
  DFailure [msg] msg.

(* fmap *)
Definition dfmap {A B : Type} (d : debug A) (f : A -> B) : debug B :=
  match d with
  | DSuccess trace v => DSuccess trace (f v)
  | DFailure trace e => DFailure trace e
  end.

Infix "<$$>" := dfmap (at level 50, left associativity).

(*----Combinators----*)

(* Map a fallible function over a list, collecting results and traces *)
Definition debug_map {A B : Type} (f : A -> debug B) (l : list A) : debug (list B) :=
  fold_left (fun acc x =>
    acc >>~ fun xs =>
    f x >>~ fun y =>
    dreturn (xs ++ [y])%list
  ) l (dreturn []).

(* Fold with a fallible function, threading traces *)
Definition debug_fold {A B : Type} (f : B -> A -> debug B) (init : B) (l : list A) : debug B :=
  fold_left (fun acc x => acc >>~ fun b => f b x) l (dreturn init).

(* Like debug_map but also logs each element using a show function *)
Definition debug_map_logged {A B : Type}
    (show_a : A -> string)
    (f : A -> debug B)
    (l : list A) : debug (list B) :=
  fold_left (fun acc x =>
    acc >>~ fun xs =>
    dtrace ("processing: " ++ show_a x) >>~ fun _ =>
    f x >>~ fun y =>
    dreturn (xs ++ [y])%list
  ) l (dreturn []).

(* Run a debug computation purely for its trace, discarding the value *)
Definition debug_ignore {A : Type} (d : debug A) : debug unit :=
  d >>~ fun _ => dreturn tt.

(* Attach a label to any failure that occurs within a computation *)
Definition debug_context {A : Type} (label : string) (d : debug A) : debug A :=
  match d with
  | DSuccess trace v => DSuccess trace v
  | DFailure trace e => DFailure (("[in " ++ label ++ "]") :: trace) e
  end.

(* Log the result of a computation before passing it on *)
Definition debug_log_result {A : Type} (show_a : A -> string) (d : debug A) : debug A :=
  d >>~ fun v =>
  dtrace ("result: " ++ show_a v) >>~ fun _ =>
  dreturn v.

(* Sequence two debug computations, keeping both traces, returning the second value *)
Definition debug_seq {A B : Type} (d1 : debug A) (d2 : debug B) : debug B :=
  d1 >>~ fun _ => d2.

(* Lift an option into debug, failing with a given message if None *)
Definition debug_of_option {A : Type} (msg : string) (o : option A) : debug A :=
  match o with
  | Some v => dreturn v
  | None   => dfail msg
  end.

(*----Pretty Printing----*)

Fixpoint format_trace (trace : list string) : string :=
  match trace with
  | []          => ""
  | [msg]       => msg
  | msg :: rest => msg ++ "
" ++ format_trace rest
  end.

Definition summarize {A : Type} (d : debug A) : string :=
  match d with
  | DSuccess trace _ =>
    "[SUCCESS] Trace:
" ++ format_trace trace
  | DFailure trace e =>
    "[FAILURE: " ++ e ++ "] Trace:
" ++ format_trace trace
  end.

(* Like summarize but also shows the value on success *)
Definition summarize_with {A : Type} (show_a : A -> string) (d : debug A) : string :=
  match d with
  | DSuccess trace v =>
    "[SUCCESS: " ++ show_a v ++ "] Trace:
" ++ format_trace trace
  | DFailure trace e =>
    "[FAILURE: " ++ e ++ "] Trace:
" ++ format_trace trace
  end.