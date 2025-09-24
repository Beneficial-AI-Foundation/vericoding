-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_profit_loss (investment : Nat) (changes : List Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_profit_loss_format 
  (investment : Nat) 
  (changes : List Int)
  (h1 : 1 ≤ investment ∧ investment ≤ 10^7)
  (h2 : changes.length ≥ 1 ∧ changes.length ≤ 100) 
  (h3 : ∀ x ∈ changes, -99 ≤ x ∧ x ≤ 99) :
  let result := calculate_profit_loss investment changes
  (result.get 0 = '+' ∨ result.get 0 = '-' ∨ result = "0") :=
  sorry

theorem calculate_profit_loss_precision
  (investment : Nat)
  (changes : List Int) 
  (h1 : 1 ≤ investment ∧ investment ≤ 10^7)
  (h2 : changes.length ≥ 1 ∧ changes.length ≤ 100)
  (h3 : ∀ x ∈ changes, -99 ≤ x ∧ x ≤ 99)
  (h4 : calculate_profit_loss investment changes ≠ "0") :
  let result := calculate_profit_loss investment changes
  String.length result ≤ 6 :=
  sorry

theorem zero_changes_result
  (investment : Nat)
  (changes : List Int)
  (h1 : 1 ≤ investment ∧ investment ≤ 10^7) 
  (h2 : changes.length ≥ 1 ∧ changes.length ≤ 100)
  (h3 : ∀ x ∈ changes, x = 0) :
  calculate_profit_loss investment changes = "0" :=
  sorry

theorem single_change_calculation
  (investment : Nat)
  (change : Int)
  (h1 : 1 ≤ investment ∧ investment ≤ 10^7)
  (h2 : -99 ≤ change ∧ change ≤ 99) :
  let result := calculate_profit_loss investment [change]
  let resultNum := String.toInt! result
  (resultNum - change).natAbs ≤ 1 :=
  sorry
-- </vc-theorems>