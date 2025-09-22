-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countAndSay (n: Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem countAndSay_one : countAndSay 1 = "1" :=
sorry

theorem countAndSay_nonempty (n: Nat) (h: n > 0) :
  (countAndSay n).length > 0 :=
sorry

theorem countAndSay_digits_only (n: Nat) (h: n > 0) :
  ∀ p: String.Pos,
    '0' ≤ (countAndSay n).get p ∧ (countAndSay n).get p ≤ '9' :=
sorry

theorem countAndSay_inductive_step (n: Nat) (h: n > 1) :
  ∃ counts digits: List Nat,
    counts.length = digits.length ∧
    (∀ d ∈ digits, d ≤ 9) ∧
    (∀ c ∈ counts, c > 0) ∧
    countAndSay n = String.join (List.map (λ (p: Nat × Nat) => toString p.1 ++ toString p.2)
                                        (List.zip counts digits)) :=
sorry
-- </vc-theorems>