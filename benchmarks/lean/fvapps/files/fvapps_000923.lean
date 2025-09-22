-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Building := Int × Int × Int × Int

def av (buildings : List Building) : Int :=
  sorry

def val (buildings : List Building) : Int :=
  sorry

def diff (l1 l2 : List Building) : List Building :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem av_nonnegative (buildings : List Building) :
  av buildings ≥ 0 :=
sorry

theorem val_nonnegative (buildings : List Building) :
  val buildings ≥ 0 :=
sorry

theorem av_sum_fourth (buildings : List Building) :
  av buildings = buildings.foldl (λ acc b => acc + b.2.2.2) 0 :=
sorry

theorem val_sum_third (buildings : List Building) :
  val buildings = buildings.foldl (λ acc b => acc + b.2.2.1) 0 :=
sorry

theorem diff_properties (l1 l2 : List Building) :
  ∀ x ∈ diff l1 l2, x ∈ l1 ∧ x ∉ l2 :=
sorry
-- </vc-theorems>