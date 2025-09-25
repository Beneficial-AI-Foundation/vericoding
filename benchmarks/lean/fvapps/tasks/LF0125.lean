-- <vc-preamble>
def MOD := 1000000007
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def profitable_schemes (G : Nat) (P : Nat) (group : List Nat) (profit : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem profitable_schemes_non_negative (G P : Nat) (group profit : List Nat) :
  profitable_schemes G P group profit ≥ 0 :=
sorry

theorem profitable_schemes_mod_bound (G P : Nat) (group profit : List Nat) :
  profitable_schemes G P group profit < MOD :=
sorry

theorem profitable_schemes_empty_zero_profit (G : Nat) :
  profitable_schemes G 0 [] [] = 1 :=
sorry

theorem profitable_schemes_empty_positive_profit (G P : Nat) :
  P > 0 → profitable_schemes G P [] [] = 0 :=
sorry

theorem profitable_schemes_scaling (G P : Nat) (group profit : List Nat) :
  group ≠ [] →
  profit.length = group.length →
  profitable_schemes G P group profit =
  profitable_schemes G (2 * P) group (List.map (fun p => 2 * p) profit) :=
sorry
-- </vc-theorems>