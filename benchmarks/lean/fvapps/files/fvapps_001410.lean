-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_left_fraction (a b n : Nat) : Nat × Nat := sorry

theorem find_left_fraction_properties {a b n : Nat}
  (ha : 2 ≤ a) (hb : 3 ≤ b) (hn : 3 ≤ n)
  (hab : a < b) (hbn : b ≤ n) :
  let (num, den) := find_left_fraction a b n
  -- Result is proper fraction within bounds
  0 < num ∧ num < den ∧ den ≤ n ∧
  -- Result is less than target
  num * b < a * den ∧
  -- Result is maximal among such fractions
  ∀ n2 d : Nat,
    1 ≤ d → d ≤ n →
    1 ≤ n2 → n2 < d →
    n2 * b < a * d →
    n2 * den ≤ num * d := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_left_fraction_reduced {a b n : Nat}
  (ha : 2 ≤ a) (hb : 3 ≤ b) (hn : 3 ≤ n)
  (hab : a < b) (hbn : b ≤ n) :
  let (num, den) := find_left_fraction a b n
  ∀ k : Nat,
    k > 1 →
    ¬(k ∣ num ∧ k ∣ den) := sorry
-- </vc-theorems>