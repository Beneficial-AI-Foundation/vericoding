-- <vc-preamble>
def BIT (n : Nat) : Type := Unit
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BIT.add (bit : BIT n) (i j v : Nat) : Unit :=
sorry

def BIT.get_val (bit : BIT n) (i : Nat) : Nat :=
sorry

def BIT.mk (n : Nat) : BIT n :=
sorry

def solve_tree_queries (n : Nat) (costs : List Nat) (edges : List (List Nat)) (queries : List (List Nat)) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bit_get_after_add (n i : Nat) (h : i < n) :
  let bit := BIT.mk n
  let _ := bit.add i (i+1) 1
  bit.get_val i = 1 :=
sorry

theorem bit_accumulate_adds (n i : Nat) (h : i < n - 1) :
  let bit := BIT.mk n
  let _ := bit.add i (i+1) 1
  let _ := bit.add i (i+1) 1
  bit.get_val i = 2 :=
sorry

theorem solve_tree_queries_initial_cost
  (n : Nat) (costs : List Nat) (edges : List (List Nat)) (h : n ≥ 2) :
  let queries := [[2,1]]
  let result := solve_tree_queries n costs [[1,2]] queries
  List.get! result 0 = List.get! costs 0 :=
sorry

theorem solve_tree_queries_update
  (n : Nat) (costs : List Nat) (edges : List (List Nat)) (val : Nat) (h : n ≥ 2) :
  let queries := [[1,1,val], [2,1]]
  let result := solve_tree_queries n costs [[1,2]] queries
  List.get! result 0 = List.get! costs 0 + val :=
sorry
-- </vc-theorems>