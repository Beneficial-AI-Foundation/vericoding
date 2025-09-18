-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def beasts (heads tails : Int) : Option (Int × Int) := sorry

theorem beasts_valid_solution {heads tails : Int} (orthus hydra : Int) 
  (h : beasts heads tails = some (orthus, hydra)) : 
  orthus * 2 + hydra * 5 = heads ∧ orthus + hydra = tails := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem beasts_negative_inputs {n : Int} (h : n < 0) :
  beasts n n = none ∧ beasts n 0 = none ∧ beasts 0 n = none := sorry

theorem beasts_zero :
  beasts 0 0 = some (0, 0) := sorry

theorem beasts_impossible_ratios {n : Int} (h : n > 0) :
  beasts n 0 = none ∧ 
  beasts (6*n) n = none ∧
  beasts n n = none := sorry
-- </vc-theorems>