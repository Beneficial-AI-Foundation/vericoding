-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def membership (amount platinum gold silver bronze : Nat) : String := sorry 

theorem membership_result_valid (amount platinum gold silver bronze : Nat)
  (h_thresholds : platinum > gold ∧ gold > silver ∧ silver > bronze) :
  membership amount platinum gold silver bronze = "Platinum" ∨ 
  membership amount platinum gold silver bronze = "Gold" ∨
  membership amount platinum gold silver bronze = "Silver" ∨ 
  membership amount platinum gold silver bronze = "Bronze" ∨
  membership amount platinum gold silver bronze = "Not a member" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem membership_platinum (amount platinum gold silver bronze : Nat)
  (h_thresholds : platinum > gold ∧ gold > silver ∧ silver > bronze)
  (h_amount : amount ≥ platinum) :
  membership amount platinum gold silver bronze = "Platinum" := sorry

theorem membership_gold (amount platinum gold silver bronze : Nat)
  (h_thresholds : platinum > gold ∧ gold > silver ∧ silver > bronze)
  (h_amount : amount ≥ gold ∧ amount < platinum) :
  membership amount platinum gold silver bronze = "Gold" := sorry

theorem membership_silver (amount platinum gold silver bronze : Nat)
  (h_thresholds : platinum > gold ∧ gold > silver ∧ silver > bronze)
  (h_amount : amount ≥ silver ∧ amount < gold) :
  membership amount platinum gold silver bronze = "Silver" := sorry

theorem membership_bronze (amount platinum gold silver bronze : Nat)
  (h_thresholds : platinum > gold ∧ gold > silver ∧ silver > bronze)
  (h_amount : amount ≥ bronze ∧ amount < silver) :
  membership amount platinum gold silver bronze = "Bronze" := sorry

theorem membership_none (amount platinum gold silver bronze : Nat)
  (h_thresholds : platinum > gold ∧ gold > silver ∧ silver > bronze)
  (h_amount : amount < bronze) :
  membership amount platinum gold silver bronze = "Not a member" := sorry

theorem threshold_ordering (platinum gold silver bronze : Nat)
  (h_platinum : platinum ≥ 1000000) (h_platinum_max : platinum ≤ 10000000)
  (h_gold : gold ≥ 100000) (h_silver : silver ≥ 10000) (h_bronze : bronze ≥ 1000) :
  platinum > gold ∧ gold > silver ∧ silver > bronze := sorry
-- </vc-theorems>