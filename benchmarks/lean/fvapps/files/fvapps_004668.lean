-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sel_number (n : Nat) (d : Nat) : Nat :=
  sorry

def hasAscendingUniqueDigits (n : Nat) : Bool :=
  sorry

def countAscendingUnique (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sel_number_non_negative (n d : Nat) :
  sel_number n d ≥ 0 :=
sorry

theorem sel_number_under_twelve (n d : Nat) :
  n < 12 → sel_number n d = 0 :=
sorry

theorem sel_number_unique_bound (n : Nat) :
  sel_number n 0 ≤ String.length (toString n) :=
sorry

theorem sel_number_monotonic_d (n : Nat) :
  ∀ d₁ d₂ : Nat, d₁ ≤ d₂ → d₂ < 10 → n ≥ 12 →
    sel_number n d₁ ≤ sel_number n d₂ :=
sorry

theorem sel_number_monotonic_n (d n₁ n₂ : Nat) :
  n₁ ≤ n₂ → n₁ ≥ 12 → d < 10 →
    sel_number n₁ d ≤ sel_number n₂ d :=
sorry
-- </vc-theorems>