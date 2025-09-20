-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pass_the_bill (total conservative reformist : Nat) : Int := sorry

def majority (total : Nat) : Nat := total/2 + 1
-- </vc-definitions>

-- <vc-theorems>
theorem pass_the_bill_valid_output (total conservative reformist : Nat) 
  (h1 : conservative + reformist ≤ total) :
  let result := pass_the_bill total conservative reformist
  result = -1 ∨ result = 0 ∨ result > 0 := sorry

theorem conservative_majority_blocks (total conservative reformist : Nat)
  (h1 : conservative + reformist ≤ total)
  (h2 : conservative ≥ majority total) :
  pass_the_bill total conservative reformist = 0 := sorry

theorem insufficient_support_fails (total conservative reformist : Nat)
  (h1 : conservative + reformist ≤ total)
  (h2 : conservative + (total - conservative - reformist) < majority total) :
  pass_the_bill total conservative reformist = -1 := sorry

theorem minimum_independents_needed (total conservative reformist : Nat)
  (h1 : conservative + reformist ≤ total)
  (h2 : pass_the_bill total conservative reformist > 0) :
  let result := pass_the_bill total conservative reformist
  let ind := total - conservative - reformist
  conservative + result ≥ majority total ∧ 
  conservative + (result - 1) < majority total ∧
  result ≤ ind := sorry

theorem result_within_bounds (total conservative reformist : Nat)
  (h1 : conservative + reformist ≤ total) :
  let result := pass_the_bill total conservative reformist
  result = -1 ∨ result = 0 ∨ (result > 0 ∧ result ≤ total) := sorry
-- </vc-theorems>