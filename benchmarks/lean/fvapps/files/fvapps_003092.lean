-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def womens_age (n : Nat) : String := sorry

theorem womens_age_starts_with (n : Nat) (h : n ≥ 2) : 
  (womens_age n).startsWith s!"{n}? That's just" = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem womens_age_ends_with (n : Nat) (h : n ≥ 2) :
  (womens_age n).endsWith "!" = true := sorry

theorem womens_age_value_20_or_21 (n : Nat) (h : n ≥ 2) :
  let val := String.toNat! ((womens_age n).split (· == ' ') |>.get! 3)
  val = 20 ∨ val = 21 := sorry

theorem womens_age_base_is_div2 (n : Nat) (h : n ≥ 2) :
  let base := String.toNat! ((womens_age n).split (· == ' ') |>.get! 5)
  base = n / 2 := sorry

theorem womens_age_even_20_odd_21 (n : Nat) (h : n ≥ 2) :
  let val := String.toNat! ((womens_age n).split (· == ' ') |>.get! 3)
  (n % 2 = 0 → val = 20) ∧ (n % 2 = 1 → val = 21) := sorry
-- </vc-theorems>