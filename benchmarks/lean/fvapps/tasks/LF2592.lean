-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gimme (arr : List Float) : Nat :=
  sorry

def sort (xs : List Float) : List Float :=
  sorry

def sortInt (xs : List Int) : List Int :=
  sorry

def gimmeInt (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gimme_in_range {arr : List Float} (h : arr.length = 3) :
  let res := gimme arr
  0 ≤ res ∧ res ≤ 2 :=
sorry

theorem gimme_gives_middle {arr : List Float} (h : arr.length = 3) :
  let sorted := sort arr
  let res := gimme arr
  arr[res]! = sorted[1]! :=
sorry

theorem gimme_integers_in_range {arr : List Int} (h : arr.length = 3) :
  let res := gimmeInt arr
  0 ≤ res ∧ res ≤ 2 :=
sorry

theorem gimme_integers_middle {arr : List Int} (h : arr.length = 3) :
  let sorted := sortInt arr
  let res := gimmeInt arr
  arr[res]! = sorted[1]! :=
sorry

theorem gimme_preserves_input {arr : List Float} (h : arr.length = 3) :
  let original := arr
  let _ := gimme arr
  arr = original :=
sorry
-- </vc-theorems>