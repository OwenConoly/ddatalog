From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog FancyNotations.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

(* Operator meanings *)
(* ================================================================= *)
(* Disj = \/          Boolean OR *)
(* Conj = /\          Boolean AND *)
(* Not = ~            Boolean NOT *)
(* Parallel = +       Parallel composition *)
(* Seq = ;            Sequential composition *)
(* Star = *           Kleene star / repetition *)
(* Assn = :=          Assignment *)
(* Match = ==         Boolean Check *)
(* Drop = 0           Annihilation / zero element *)
(* Id = 1             Identity element *)

(* ================= Associativity ================= *)

(* a \/ (b \/ c) -> (a \/ b) \/ c *)
Definition r_disj_assoc_l : rule :=
  datalog_rule:(
    [ Term(Disj(Disj($a, $b), $c));
      rewrite(
        Disj($a, Disj($b, $c)),
        Disj(Disj($a, $b), $c)
      )
    ]
    :-
    [ Term(Disj($a, Disj($b, $c))) ]
  ).

(* (a \/ b) \/ c -> a \/ (b \/ c) *)
Definition r_disj_assoc_r : rule :=
  datalog_rule:(
    [ Term(Disj($a, Disj($b, $c)));
      rewrite(
        Disj(Disj($a, $b), $c),
        Disj($a, Disj($b, $c))
      )
    ]
    :-
    [ Term(Disj(Disj($a, $b), $c)) ]
  ).

(* a /\ (b /\ c) -> (a /\ b) /\ c *)
Definition r_conj_assoc_l : rule :=
  datalog_rule:(
    [ Term(Conj(Conj($a, $b), $c));
      rewrite(
        Conj($a, Conj($b, $c)),
        Conj(Conj($a, $b), $c)
      )
    ]
    :-
    [ Term(Conj($a, Conj($b, $c))) ]
  ).

(* (a /\ b) /\ c -> a /\ (b /\ c) *)
Definition r_conj_assoc_r : rule :=
  datalog_rule:(
    [ Term(Conj($a, Conj($b, $c)));
      rewrite(
        Conj(Conj($a, $b), $c),
        Conj($a, Conj($b, $c))
      )
    ]
    :-
    [ Term(Conj(Conj($a, $b), $c)) ]
  ).

(* p + (q + r) -> (p + q) + r *)
Definition r_parallel_assoc_l : rule :=
  datalog_rule:(
    [ Term(Parallel(Parallel($p, $q), $r));
      rewrite(
        Parallel($p, Parallel($q, $r)),
        Parallel(Parallel($p, $q), $r)
      )
    ]
    :-
    [ Term(Parallel($p, Parallel($q, $r))) ]
  ).

(* (p + q) + r -> p + (q + r) *)
Definition r_parallel_assoc_r : rule :=
  datalog_rule:(
    [ Term(Parallel($p, Parallel($q, $r)));
      rewrite(
        Parallel(Parallel($p, $q), $r),
        Parallel($p, Parallel($q, $r))
      )
    ]
    :-
    [ Term(Parallel(Parallel($p, $q), $r)) ]
  ).

(* (p ; q) ; r -> p ; (q ; r) *)
Definition r_seq_assoc_l : rule :=
  datalog_rule:(
    [ Term(Seq(Seq($p, $q), $r));
      rewrite(
        Seq($p, Seq($q, $r)),
        Seq(Seq($p, $q), $r)
      )
    ]
    :-
    [ Term(Seq($p, Seq($q, $r))) ]
  ).


(* p ; (q ; r) -> (p ; q) ; r *)
Definition r_seq_assoc_r : rule :=
  datalog_rule:(
    [ Term(Seq($p, Seq($q, $r)));
      rewrite(
        Seq(Seq($p, $q), $r),
        Seq($p, Seq($q, $r))
      )
    ]
    :-
    [ Term(Seq(Seq($p, $q), $r)) ]
  ).

(* ================= Commutativity ================= *)

(* a \/ b -> b \/ a *)
Definition r_disj_comm : rule :=
  datalog_rule:(
    [ Term(Disj($b, $a));
      rewrite(
        Disj($a, $b),
        Disj($b, $a)
      )
    ]
    :-
    [ Term(Disj($a, $b)) ]
  ).

(* a /\ b -> b /\ a *)
Definition r_conj_comm : rule :=
  datalog_rule:(
    [ Term(Conj($b, $a));
      rewrite(
        Conj($a, $b),
        Conj($b, $a)
      )
    ]
    :-
    [ Term(Conj($a, $b)) ]
  ).

(* p + q -> q + p *)
Definition r_parallel_comm : rule :=
  datalog_rule:(
    [ Term(Parallel($q, $p));
      rewrite(
        Parallel($p, $q),
        Parallel($q, $p)
      )
    ]
    :-
    [ Term(Parallel($p, $q)) ]
  ).

(* ================= Identities ================= *)

(* a \/ 0 -> a *)
Definition r_disj_id : rule :=
  datalog_rule:(
    [ Term($a);
      rewrite(
        Disj($a, Drop ( )),
        $a
      )
    ]
    :-
    [ Term(Disj($a, Drop ( ))) ]
  ).

(* p + 0 -> p *)
Definition r_parallel_filter_drop : rule :=
  datalog_rule:(
    [ Term($p);
      rewrite(
        Parallel($p, Filter(Drop ( ))),
        $p
      )
    ]
    :-
    [ Term(Parallel($p, Filter(Drop ( )))) ]
  ).

(* a /\ 1 -> a *)
Definition r_conj_id : rule :=
  datalog_rule:(
    [ Term($a);
      rewrite(
        Conj($a, Id ( ) ),
        $a
      )
    ]
    :-
    [ Term(Conj($a, Id ( ) )) ]
  ).

(* 1 ; p -> p *)
Definition r_seq_filter_id_l : rule :=
  datalog_rule:(
    [ Term($p);
      rewrite(
        Seq(Filter(Id ( )), $p),
        $p
      )
    ]
    :-
    [ Term(Seq(Filter(Id ( )), $p)) ]
  ).

(* p ; 1 -> p *)
Definition r_seq_filter_id_r : rule :=
  datalog_rule:(
    [ Term($p);
      rewrite(
        Seq($p, Filter(Id ( ))),
        $p
      )
    ]
    :-
    [ Term(Seq($p, Filter(Id ( )))) ]
  ).

(* ================= Annihilation ================= *)

(* a /\ 0 -> 0 *)
Definition r_conj_drop : rule :=
  datalog_rule:(
    [ Term(Drop ( ));
      rewrite(
        Conj($a, Drop ( )),
        Drop ( )
      )
    ]
    :-
    [ Term(Conj($a, Drop ( ))) ]
  ).

(* p ; 0 -> 0 *)
Definition r_seq_filter_drop_l : rule :=
  datalog_rule:(
    [ Term(Filter(Drop ( )));
      rewrite(
        Seq(Filter(Drop ( )), $p),
        Filter(Drop ( ))
      )
    ]
    :-
    [ Term(Seq(Filter(Drop ( )), $p)) ]
  ).

(* 0 ; p -> 0 *)
Definition r_seq_filter_drop_r : rule :=
  datalog_rule:(
    [ Term(Filter(Drop ( )));
      rewrite(
        Seq($p, Filter(Drop ( ))),
        Filter(Drop ( ))
      )
    ]
    :-
    [ Term(Seq($p, Filter(Drop ( )))) ]
  ).

(* ================= Idempotence ================= *)

(* a \/ a -> a *)
Definition r_disj_idempotent : rule :=
  datalog_rule:(
    [ Term($a);
      rewrite(
        Disj($a, $a),
        $a
      )
    ]
    :-
    [ Term(Disj($a, $a)) ]
  ).

(* p + p -> p *)
Definition r_parallel_idempotent : rule :=
  datalog_rule:(
    [ Term($p);
      rewrite(
        Parallel($p, $p),
        $p
      )
    ]
    :-
    [ Term(Parallel($p, $p)) ]
  ).

(* ================= Distributivity ================= *)

(* a /\ (b \/ c) -> (a /\ b) \/ (a /\ c) *)
Definition r_conj_disj_dist_l : rule :=
  datalog_rule:(
    [ Term(Disj(Conj($a, $b), Conj($a, $c)));
      rewrite(
        Conj($a, Disj($b, $c)),
        Disj(Conj($a, $b), Conj($a, $c))
      )
    ]
    :-
    [ Term(Conj($a, Disj($b, $c))) ]
  ).

(* (a /\ b) \/ (a /\ c) -> a /\ (b \/ c) *)
Definition r_conj_disj_dist_r : rule :=
  datalog_rule:(
    [ Term(Conj($a, Disj($b, $c)));
      rewrite(
        Disj(Conj($a, $b), Conj($a, $c)),
        Conj($a, Disj($b, $c))
      )
    ]
    :-
    [ Term(Disj(Conj($a, $b), Conj($a, $c))) ]
  ).

(* ================= Boolean Algebra Axioms ================= *)

(* a \/ 1 -> 1 *)
Definition r_disj_id_plus : rule :=
  datalog_rule:(
    [ Term(Id ( ));
      rewrite(
        Disj($a, Id ( )),
        Id ( )
      )
    ]
    :-
    [ Term(Disj($a, Id ( ))) ]
  ).

(* a \/ ~a -> 1 *)
Definition r_disj_not : rule :=
  datalog_rule:(
    [ Term(Id ( ));
      rewrite(
        Disj($a, Not($a)),
        Id ( )
      )
    ]
    :-
    [ Term(Disj($a, Not($a))) ]
  ).

(* a /\ ~a -> 0 *)
Definition r_conj_not : rule :=
  datalog_rule:(
    [ Term(Drop ( ));
      rewrite(
        Conj($a, Not($a)),
        Drop ( )
      )
    ]
    :-
    [ Term(Conj($a, Not($a))) ]
  ).

(* ================= Packet / Sequential Axioms ================= *)

(* f1 := n1 ; f2 := n2 -> f2 := n2 ; f1 := n1 when f1 != f2*)
(* TODO encode the NEQ for f1 and f2 *)
Definition r_mod_comm : rule :=
  datalog_rule:(
    [ Term(Seq(Assn($f2, $n2), Assn($f1, $n1)));
      rewrite(
        Seq(Assn($f1, $n1), Assn($f2, $n2)),
        Seq(Assn($f2, $n2), Assn($f1, $n1))
      )
    ]
    :-
    [ Term(Seq(Assn($f1, $n1), Assn($f2, $n2))) ]
  ).

(* f1 := n1 ; f2 == n2 -> f2 == n2 ; f1 := n1 when f2 != f1 *)
Definition r_mod_filter_comm1 : rule :=
  datalog_rule:(
    [ Term(Seq(Assn($f1, $n1), Filter(Match($f2, $n2))));
      rewrite(
        Seq(Filter(Match($f2, $n2)), Assn($f1, $n1)),
        Seq(Assn($f1, $n1), Filter(Match($f2, $n2)))
      )
    ]
    :-
    [ Term(Seq(Assn($f1, $n1), Filter(Match($f2, $n2)))) ]
  ).

(* f1 == n1 ; f2 := n2 -> f2 := n2 ; f1 == n1 when f2 != f1 *)
Definition r_mod_filter_comm2 : rule :=
  datalog_rule:(
    [ Term(Seq(Filter(Match($f1, $n1)), Assn($f2, $n2)));
      rewrite(
        Seq(Assn($f2, $n2), Filter(Match($f1, $n1))),
        Seq(Filter(Match($f1, $n1)), Assn($f2, $n2))
      )
    ]
    :-
    [ Term(Seq(Filter(Match($f1, $n1)), Assn($f2, $n2))) ]
  ).

(* f := n ; f == n -> f := n *)
Definition r_mod_filter : rule :=
  datalog_rule:(
    [ Term(Assn($f, $n));
      rewrite(
        Seq(Assn($f, $n), Filter(Match($f, $n))),
        Assn($f, $n)
      )
    ]
    :-
    [ Term(Seq(Assn($f, $n), Filter(Match($f, $n)))) ]
  ).

(* f == n ; f := n -> f == n *)
Definition r_filter_mod : rule :=
  datalog_rule:(
    [ Term(Filter(Match($f, $n)));
      rewrite(
        Seq(Filter(Match($f, $n)), Assn($f, $n)),
        Filter(Match($f, $n))
      )
    ]
    :-
    [ Term(Seq(Filter(Match($f, $n)), Assn($f, $n))) ]
  ).

(* f == n1 ; f == n2 -> 0 when n1 != n2 *)
(* TODO encode the NEQ for n1 and n2 *)
Definition r_filter_contradiction : rule :=
  datalog_rule:(
    [ Term(Filter(Drop ( )));
      rewrite(
        Seq(Filter(Match($f, $n1)), Filter(Match($f, $n2))),
        Filter(Drop ( ))
      )
    ]
    :-
    [ Term(Seq(Filter(Match($f, $n1)), Filter(Match($f, $n2)))) ]
  ).

(* f := n ; f := n -> f := n *)
Definition r_twice_mod : rule :=
  datalog_rule:(
    [ Term(Assn($f, $n));
      rewrite(
        Seq(Assn($f, $n), Assn($f, $n)),
        Assn($f, $n)
      )
    ]
    :-
    [ Term(Seq(Assn($f, $n), Assn($f, $n))) ]
  ).

(* ================= Equality Between Algebras ================= *)

(* a \/ b -> Filter a + Filter b *)
Definition r_filter_disj : rule :=
  datalog_rule:(
    [ Term(Parallel(Filter($a), Filter($b)));
      rewrite(
        Filter(Disj($a, $b)),
        Parallel(Filter($a), Filter($b))
      )
    ]
    :-
    [ Term(Filter(Disj($a, $b))) ]
  ).

(* Filter a + Filter b -> Filter (a \/ b) *)
Definition r_parallel_filter : rule :=
  datalog_rule:(
    [ Term(Filter(Disj($a, $b)));
      rewrite(
        Parallel(Filter($a), Filter($b)),
        Filter(Disj($a, $b))
      )
    ]
    :-
    [ Term(Parallel(Filter($a), Filter($b))) ]
  ).

(* Filter(a) ; Filter(b) -> Filter(a /\ b) *)
Definition r_filter_conj : rule :=
  datalog_rule:(
    [ Term(Filter(Conj($a, $b)));
      rewrite(
        Seq(Filter($a), Filter($b)),
        Filter(Conj($a, $b))
      )
    ]
    :-
    [ Term(Seq(Filter($a), Filter($b))) ]
  ).

(* Filter(a) ; Filter(b) -> Filter(a /\ b) *)
Definition r_seq_filter : rule :=
  datalog_rule:(
    [ Term(Seq(Filter($a), Filter($b)));
      rewrite(
        Filter(Conj($a, $b)),
        Seq(Filter($a), Filter($b))
      )
    ]
    :-
    [ Term(Seq(Filter($a), Filter($b))) ]
  ).

Definition r_backwards_congruence : rule :=
  datalog_rule:(
    [ rewrite($a, $b) ]
    :-
    [ rewrite(Filter($a), Filter($b)) ]
  ).

Definition r_rewrite_transitive : rule :=
  datalog_rule:(
    [ rewrite($a, $c) ]
    :-
    [ rewrite($a, $b);
      rewrite($b, $c)
    ]
  ).

(* ================= Term Closure Rules ================= *)

(* If Disj(a, b) is a term, then a and b are terms *)
Definition r_disj_subterms : rule :=
  datalog_rule:(
    [ Term($a); Term($b) ]
    :-
    [ Term(Disj($a, $b)) ]
  ).

(* If Conj(a, b) is a term, then a and b are terms *)
Definition r_conj_subterms : rule :=
  datalog_rule:(
    [ Term($a); Term($b) ]
    :-
    [ Term(Conj($a, $b)) ]
  ).

(* If Seq(p, q) is a term, then p and q are terms *)
Definition r_seq_subterms : rule :=
  datalog_rule:(
    [ Term($p); Term($q) ]
    :-
    [ Term(Seq($p, $q)) ]
  ).

(* If Parallel(p, q) is a term, then p and q are terms *)
Definition r_parallel_subterms : rule :=
  datalog_rule:(
    [ Term($p); Term($q) ]
    :-
    [ Term(Parallel($p, $q)) ]
  ).

(* If Filter(a) is a term, then a is a term *)
Definition r_filter_subterm : rule :=
  datalog_rule:(
    [ Term($a) ]
    :-
    [ Term(Filter($a)) ]
  ).

(* If Not(a) is a term, then a is a term *)
Definition r_not_subterm : rule :=
  datalog_rule:(
    [ Term($a) ]
    :-
    [ Term(Not($a)) ]
  ).


(* ================= Program ================= *)

Definition netkat_program : list rule :=
  [
    r_disj_assoc_l; r_disj_assoc_r;
    r_conj_assoc_l; r_conj_assoc_r;
    r_parallel_assoc_l; r_parallel_assoc_r;
    r_seq_assoc_l; r_seq_assoc_r;
    r_disj_comm; r_conj_comm; r_parallel_comm;
    r_disj_id; r_parallel_filter_drop; r_conj_id;
    r_seq_filter_id_l; r_seq_filter_id_r;
    r_conj_drop; r_seq_filter_drop_l; r_seq_filter_drop_r;
    r_disj_idempotent; r_parallel_idempotent;
    r_conj_disj_dist_l; r_conj_disj_dist_r;
    r_disj_id_plus; r_disj_not; r_conj_not;
    r_mod_comm; r_mod_filter_comm1; r_mod_filter_comm2;
    r_mod_filter; r_filter_mod; r_filter_contradiction; r_twice_mod;
    r_filter_disj; r_parallel_filter; r_filter_conj; r_seq_filter;
    r_backwards_congruence;
    r_rewrite_transitive; r_disj_subterms; r_conj_subterms;
    r_seq_subterms; r_parallel_subterms; r_filter_subterm; r_not_subterm
  ].


(* Temp fix, may use typeclasses later *)
Definition get_program_dependencies (p : list rule) :=
  DependencyGenerator.get_program_dependencies
    (rel := rel) (var := var) (fn := fn) (aggregator := aggregator)
    (rel_eqb := rel_eqb) (expr_compatible := expr_compatible)
    p.

Definition get_rule_dependencies (p : list rule) (r : rule) :=
  DependencyGenerator.get_rule_dependencies
    (rel := rel) (var := var) (fn := fn) (aggregator := aggregator)
    (rel_eqb := rel_eqb) (expr_compatible := expr_compatible)
    p r.

Definition get_program_dependencies_flat (p : list rule) :=
  DependencyGenerator.get_program_dependencies_flat
    (rel := rel) (var := var) (fn := fn) (aggregator := aggregator)
    (aggregator_eqb := aggregator_eqb) (rel_eqb := rel_eqb)
    (expr_compatible := expr_compatible) (fn_eqb := fn_eqb) (var_eqb := var_eqb)
    p.

(* Example computations *)
Compute get_program_dependencies netkat_program.
Compute get_rule_dependencies
        netkat_program
        r_disj_subterms.

Compute get_program_dependencies_flat netkat_program.