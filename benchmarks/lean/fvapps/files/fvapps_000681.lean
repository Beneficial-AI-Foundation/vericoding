-- <vc-preamble>
def listMin (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => List.foldl min h t

def findMinValidPath (costs : List (List Nat)) : Nat :=
  let range4 := [0, 1, 2, 3]
  let maxVal := 10000
  let bank1 := costs.head!
  let bank2 := costs.get! 1
  listMin (List.map (fun w1 =>
    listMin (List.map (fun w2 =>
      if w1 ≠ w2 then bank1[w1]! + bank2[w2]! else maxVal
    ) range4)
  ) range4)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minRobberyCost (n : Nat) (costs : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_bank_result (costs : List (List Nat))
  (h1 : costs.length = 1)
  (h2 : ∀ lst ∈ costs, lst.length = 4)
  (h3 : ∀ lst ∈ costs, ∀ x ∈ lst, x > 0) :
  minRobberyCost 1 costs = listMin (costs.head!) := by
sorry

theorem two_banks_positive (costs : List (List Nat))
  (h1 : costs.length = 2)
  (h2 : ∀ lst ∈ costs, lst.length = 4)
  (h3 : ∀ lst ∈ costs, ∀ x ∈ lst, x > 0) :
  minRobberyCost 2 costs > 0 := by
sorry

theorem two_banks_lower_bound (costs : List (List Nat))
  (h1 : costs.length = 2)
  (h2 : ∀ lst ∈ costs, lst.length = 4)
  (h3 : ∀ lst ∈ costs, ∀ x ∈ lst, x > 0) :
  minRobberyCost 2 costs ≥ listMin (costs.head!) + listMin (costs.get! 1) := by
sorry

theorem two_banks_min_path (costs : List (List Nat))
  (h1 : costs.length = 2)
  (h2 : ∀ lst ∈ costs, lst.length = 4)
  (h3 : ∀ lst ∈ costs, ∀ x ∈ lst, x > 0) :
  minRobberyCost 2 costs = findMinValidPath costs := by
sorry
-- </vc-theorems>