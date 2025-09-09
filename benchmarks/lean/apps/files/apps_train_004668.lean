def sel_number (n : Nat) (d : Nat) : Nat :=
  sorry

def hasAscendingUniqueDigits (n : Nat) : Bool :=
  sorry

/- Helper function to count numbers with ascending unique digits -/

-- <vc-helpers>
-- </vc-helpers>

def countAscendingUnique (n : Nat) : Nat :=
  sorry

theorem sel_number_non_negative (n d : Nat) :
  sel_number n d ≥ 0 :=
  sorry

theorem sel_number_under_twelve (n d : Nat) :
  n < 12 → sel_number n d = 0 :=
  sorry

theorem sel_number_unique_bound (n : Nat) :
  sel_number n 0 ≤ String.length (toString n) :=
  sorry

/- Helper function to check if digits are ascending and unique -/

theorem sel_number_monotonic_d (n : Nat) :
  ∀ d₁ d₂ : Nat, d₁ ≤ d₂ → d₂ < 10 → n ≥ 12 → 
    sel_number n d₁ ≤ sel_number n d₂ :=
  sorry

theorem sel_number_monotonic_n (d n₁ n₂ : Nat) :
  n₁ ≤ n₂ → n₁ ≥ 12 → d < 10 →
    sel_number n₁ d ≤ sel_number n₂ d :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval sel_number 20 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval sel_number 0 1

/-
info: 12
-/
-- #guard_msgs in
-- #eval sel_number 50 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible