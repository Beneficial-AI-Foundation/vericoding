-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n: Nat) : List Nat :=
sorry

def visible_sum (n i: Nat) : Nat :=
sorry

def min_visible_sum (n: Nat) : Nat :=
sorry

def loneliest (n: Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem loneliest_returns_bool (n: Nat) :
  loneliest n = true ∨ loneliest n = false :=
sorry

theorem loneliest_zero_one :
  ∀ n: Nat, (∀ d: Nat, d ∈ (digits n) → d = 0 ∨ d = 1) →
  loneliest n = true ↔ ∃ i, (digits n).get? i = some 1 ∧
  (∀ j, j ≠ i → (digits n).get? j = some 0) :=
sorry

theorem loneliest_same_digit :
  ∀ n: Nat, (∀ i j: Nat, i < (digits n).length → j < (digits n).length →
    (digits n).get ⟨i, sorry⟩ = (digits n).get ⟨j, sorry⟩) →
  loneliest n = true ↔ (digits n).get ⟨0, sorry⟩ = 1 :=
sorry

theorem loneliest_no_ones :
  ∀ n: Nat, (∀ i: Nat, i < (digits n).length → (digits n).get ⟨i, sorry⟩ ≠ 1) →
  loneliest n = false :=
sorry

theorem loneliest_min_loneliness :
  ∀ n: Nat, loneliest n = true ↔
  (∃ i: Nat, (digits n).get? i = some 1 ∧
   visible_sum n i = min_visible_sum n) :=
sorry
-- </vc-theorems>