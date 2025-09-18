-- <vc-preamble>
def sumList (l : List Int) : Int := match l with
  | [] => 0
  | h::t => h + sumList t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combos (n : Int) (m : Int := 1) : List (List Int) := sorry

def isSorted (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>