-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countValidBitSwaps (n : Nat) (a : String) (b : String) : Nat :=
  sorry

def stringRepeat (s : String) (n : Nat) : String :=
  sorry

def makeAlternatingString (n : Nat) (startBit : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem countValidBitSwaps_returns_natural (n : Nat) (a : String) (b : String)
  (h1 : a.length = n) (h2 : b.length = n) :
  ∃ (m : Nat), countValidBitSwaps n a b = m := by
sorry

theorem countValidBitSwaps_nonnegative (n : Nat) (a : String) (b : String)
  (h1 : a.length = n) (h2 : b.length = n) :
  countValidBitSwaps n a b ≥ 0 := by
sorry

theorem countValidBitSwaps_all_zeros (n : Nat) :
  countValidBitSwaps n (stringRepeat "0" n) (stringRepeat "0" n) = 0 := by
sorry

theorem countValidBitSwaps_all_ones (n : Nat) :
  countValidBitSwaps n (stringRepeat "1" n) (stringRepeat "1" n) = 0 := by
sorry

theorem countValidBitSwaps_alternating (n : Nat) :
  let alt1 := makeAlternatingString n "0"
  let alt2 := makeAlternatingString n "1"
  ∃ (m : Nat), countValidBitSwaps n alt1 alt2 = m := by
sorry
-- </vc-theorems>