-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_number (costs : List Nat) (target : Int) : String := sorry

theorem largest_number_output_properties
  (costs : List Nat) 
  (target : Int)
  (h1 : costs.length = 9)
  (h2 : ∀ x ∈ costs, 1 ≤ x ∧ x ≤ 100)
  (h3 : 1 ≤ target ∧ target ≤ 100) :
  let result := largest_number costs target
  -- Result is non-empty string
  (result.length > 0) ∧
  -- Contains only digits
  (∀ c ∈ result.data, c.isDigit) ∧
  -- Either 0 or valid cost sum
  (result = "0" ∨
    -- Sum of digit costs equals target
    (let digits := result.data.map (fun c => c.toNat - '0'.toNat)
     let costProducts := digits.zip costs |>.map (fun (d, c) => c * d)
     let cost_sum := costProducts.foldl (fun x y => x + y) (0 : Nat)
     Int.ofNat cost_sum = target)) ∧
  -- All digits between 1-9
  (result = "0" ∨ 
    (∀ d ∈ result.data.map (fun c => c.toNat - '0'.toNat), 1 ≤ d ∧ d ≤ 9)) := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_target_gives_zero 
  (costs : List Nat)
  (h1 : costs.length = 9)
  (h2 : ∀ x ∈ costs, 1 ≤ x ∧ x ≤ 100) :
  largest_number costs 0 = "0" := sorry

theorem negative_target_gives_zero
  (costs : List Nat)
  (h1 : costs.length = 9)
  (h2 : ∀ x ∈ costs, 1 ≤ x ∧ x ≤ 100) :
  ∀ target < 0, largest_number costs target = "0" := sorry

theorem impossible_costs_give_zero
  (costs : List Nat)
  (h1 : costs.length = 9)
  (h2 : ∀ x ∈ costs, x ≥ 1000) :
  largest_number costs 100 = "0" := sorry
-- </vc-theorems>