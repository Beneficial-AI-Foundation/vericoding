-- <vc-preamble>
def listMin (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h::t => t.foldl min h

partial def minFactor (n : Nat) : Nat :=
  if n ≤ 1 then 1 else
  let rec find (k : Nat) : Nat :=
    if k * k > n then n
    else if n % k = 0 then k
    else find (k + 1)
  find 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scf (nums : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scf_basic_properties (nums : List Nat) :
  let result := scf nums
  (nums ≠ [] → 1 ≤ result ∧ result ≤ listMin nums) ∧
  (nums = [] → result = 1) ∧
  (∀ n ∈ nums, n % result = 0) ∧
  (result > 1 → ¬ ∃ k, 2 ≤ k ∧ k < result ∧ ∀ n ∈ nums, n % k = 0) :=
sorry

theorem scf_identical_numbers (n : Nat) (h : n ≥ 2) :
  let nums := List.replicate 5 n
  scf nums = minFactor n :=
sorry

theorem scf_nonpositive_inputs (nums : List Nat) (h : ∀ n ∈ nums, n = 0) :
  scf nums = 1 :=
sorry
-- </vc-theorems>