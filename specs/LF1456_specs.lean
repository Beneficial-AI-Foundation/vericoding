-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_magnet_attract (n k : Nat) (s : String) : Nat :=
sorry

def countChar (s : String) (c : Char) : Nat :=
sorry

def String.atN (s : String) (n : Nat) : Char :=
sorry

def countAdjacentPairs (n : Nat) (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_magnet_blocked_by_x {n k : Nat} {s : String} :
  (∀ i j, 0 ≤ i → i < n → 0 ≤ j → j < n →
    s.atN i = 'M' → s.atN j = 'I' →
    ∃ x, min i j ≤ x ∧ x ≤ max i j ∧ s.atN x = 'X') →
  max_magnet_attract n k s = 0 :=
sorry

theorem max_magnet_distance_zero {n : Nat} {s : String} :
  max_magnet_attract n 0 s ≤ countAdjacentPairs n s :=
sorry

theorem max_magnet_output_nonNeg {n k : Nat} {s : String} :
  max_magnet_attract n k s ≥ 0 :=
sorry

theorem max_magnet_output_bounded {n k : Nat} {s : String} :
  max_magnet_attract n k s ≤ min (countChar s 'M') (countChar s 'I') :=
sorry
-- </vc-theorems>