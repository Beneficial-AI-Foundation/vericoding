-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseInvert (lst : List Int) : List Int :=
sorry

def numReverse (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverseInvert_returns_list_of_ints {lst : List Int} :
  ∀ x, x ∈ reverseInvert lst → x ∈ lst := by
sorry

theorem reverseInvert_bounded {lst : List Int}
    (h : ∀ x ∈ lst, -999 ≤ x ∧ x ≤ 999) :
    ∀ (i : Fin lst.length),
      let orig := lst.get i
      let revNum := numReverse (Int.natAbs orig)
      (reverseInvert lst).get ⟨i, by sorry⟩ = if orig > 0 then -revNum else revNum := by
sorry

theorem reverseInvert_single_digits {lst : List Int} (h : ∀ x ∈ lst, 0 ≤ x ∧ x ≤ 9) :
  ∀ (i : Fin lst.length),
    (reverseInvert lst).get ⟨i, by sorry⟩ = -(lst.get i) := by
sorry

theorem reverseInvert_length_preservation {lst : List Int} :
  (reverseInvert lst).length = lst.length := by
sorry
-- </vc-theorems>