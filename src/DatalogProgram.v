From Stdlib Require Import Strings.String.
From Datalog Require Import Datalog.
From Stdlib Require Import List.
Import ListNotations.
Open Scope string_scope.

Definition rel := string.
Definition fn := string.
Definition var := string.
Definition aggregator := string.

Definition fact := fact rel var fn.
Definition expr := expr var fn.
Definition rule := rule rel var fn aggregator.

Definition basic_rule : rule :=
  {| rule_agg := None; 
     rule_hyps := [];
     rule_concls := [] |}.

Definition more_complicated_rule : rule :=
  {| rule_agg := None;
     rule_hyps := [
      {| fact_R := "edge";
         fact_args := [(var_expr "x"); (var_expr "y")]|}
     ]; 
     rule_concls := [
       {| fact_R := "path";
         fact_args := [(var_expr "x"); (var_expr "y")]|}
     ] |}.