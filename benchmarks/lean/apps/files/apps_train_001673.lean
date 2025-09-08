/-
Jon and Joe have received equal marks in the school examination. But, they won't reconcile in peace when equated with each other. To prove his might, Jon challenges Joe to write a program to find all possible number combos that sum to a given number. While unsure whether he would be able to accomplish this feat or not, Joe accpets the challenge. Being Joe's friend, your task is to help him out.

# Task

Create a function `combos`, that accepts a single positive integer `num` (30 > `num` > 0) and returns an array of arrays of positive integers that sum to `num`.

# Notes
1. Sub-arrays may or may not have their elements sorted.
2. The order of sub-arrays inside the main array does not matter.
3. For an optimal solution, the following operation should complete within 6000ms.

# Sample
-/

def sumList (l : List Int) : Int := match l with
  | [] => 0
  | h::t => h + sumList t

-- <vc-helpers>
-- </vc-helpers>

def combos (n : Int) (m : Int := 1) : List (List Int) := sorry

def isSorted (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)

theorem sum_equals_input (n : Int) (h : n > 0) (h' : n ≤ 10) :
  ∀ combo ∈ combos n, sumList combo = n := sorry

theorem all_positive (n : Int) (h : n > 0) (h' : n ≤ 10) :
  ∀ combo ∈ combos n, ∀ x ∈ combo, x > 0 := sorry

theorem minimum_value (n m : Int) (h1 : n > 0) (h2 : n ≤ 10) (h3 : m > 0) (h4 : m ≤ 10) :
  ∀ combo ∈ combos n m, ∀ x ∈ combo, x ≥ m := sorry

theorem empty_for_invalid :
  (combos 0 = []) ∧ 
  (combos (-1) = []) ∧
  (combos 5 6 = []) := sorry

theorem output_sorted (n : Int) (h : n > 0) (h' : n ≤ 10) :
  ∀ combo ∈ combos n, isSorted combo = true := sorry

theorem result_uniqueness (n : Int) (h : n > 0) (h' : n ≤ 10) :
  List.Nodup (combos n) := sorry

/-
info: [[1]]
-/
-- #guard_msgs in
-- #eval combos 1

/-
info: sorted([[1, 1], [2]])
-/
-- #guard_msgs in
-- #eval sorted combos(2)

/-
info: sorted([[1, 1, 1], [1, 2], [3]])
-/
-- #guard_msgs in
-- #eval sorted combos(3)

-- Apps difficulty: interview
-- Assurance level: unguarded