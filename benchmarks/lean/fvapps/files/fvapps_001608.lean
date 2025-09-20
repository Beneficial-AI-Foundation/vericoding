-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isNStraightHand (hand : List Int) (w : Int) : Bool :=
  sorry

def isConsecutive (xs : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem div_by_w_necessary {hand : List Int} {w : Int}
  (hw : 0 < w) (hw' : w ≤ 10000) (hh : List.length hand > 0) :
  isNStraightHand hand w → List.length hand % w = 0 :=
sorry

theorem w_one_always_true {hand : List Int} (hh : List.length hand > 0) :
  isNStraightHand hand 1 = true :=
sorry

theorem monotonic_w {hand : List Int} {w : Int}
  (hw : 0 < w) (hw' : w < List.length hand) (hh : List.length hand > 0) :
  isNStraightHand hand w → ¬isNStraightHand hand (w + 1) :=
sorry

theorem consecutive_numbers_possible {hand : List Int}
  (hh : List.length hand > 0)
  (h_len : List.length hand ≥ 2)
  (h_consec : isConsecutive hand)
  (h_div : List.length hand % 3 = 0) :
  isNStraightHand hand 3 :=
sorry
-- </vc-theorems>