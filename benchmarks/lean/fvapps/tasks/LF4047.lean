-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_my_dollars (dollars : Float) (currency : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convert_my_dollars_valid_format 
  (dollars : Float) 
  (currency : String) 
  (h1 : dollars ≥ 0)
  (h2 : dollars ≤ 1000000) :
  ∃ amount : Float,
    convert_my_dollars dollars currency = s!"You now have {amount} of {currency}." :=
  sorry

theorem convert_my_dollars_invalid_currency
  (dollars : Nat)
  (currency : String)
  (h1 : dollars ≥ 0)
  (h2 : dollars ≤ 1000000) :
  convert_my_dollars (Float.ofNat dollars) currency = s!"You now have 0 of {currency}." :=
  sorry

theorem convert_my_dollars_scaling
  (dollars : Float)
  (h1 : dollars ≥ 0)
  (h2 : dollars ≤ 1000000) :
  let result1 := convert_my_dollars dollars "Armenian Dram"
  let result2 := convert_my_dollars (2 * dollars) "Armenian Dram"
  ∃ amount1 amount2 : Float,
    result1 = s!"You now have {amount1} of Armenian Dram." ∧ 
    result2 = s!"You now have {amount2} of Armenian Dram." ∧
    amount2 = 2 * amount1 :=
  sorry
-- </vc-theorems>