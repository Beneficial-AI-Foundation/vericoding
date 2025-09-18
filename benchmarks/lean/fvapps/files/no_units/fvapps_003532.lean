-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hex_hash (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hex_hash_returns_nat (s : String) :
  hex_hash s ≥ 0 :=
sorry

theorem hex_hash_consistent (s : String) :
  hex_hash s = hex_hash s :=
sorry

theorem empty_string_hash :
  hex_hash "" = 0 :=
sorry
-- </vc-theorems>