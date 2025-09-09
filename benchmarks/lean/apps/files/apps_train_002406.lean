-- <vc-helpers>
-- </vc-helpers>

def countAndSay (n: Nat) : String :=
  sorry

theorem countAndSay_one : countAndSay 1 = "1" :=
  sorry

/- Every output is a string of nonzero length -/

theorem countAndSay_nonempty (n: Nat) (h: n > 0) : 
  (countAndSay n).length > 0 :=
  sorry

/- The output only contains ASCII digits -/

theorem countAndSay_digits_only (n: Nat) (h: n > 0) : 
  ∀ p: String.Pos, 
    '0' ≤ (countAndSay n).get p ∧ (countAndSay n).get p ≤ '9' :=
  sorry

/- Each count-and-say result follows from the previous number -/

theorem countAndSay_inductive_step (n: Nat) (h: n > 1) :
  ∃ counts digits: List Nat, 
    counts.length = digits.length ∧ 
    (∀ d ∈ digits, d ≤ 9) ∧
    (∀ c ∈ counts, c > 0) ∧
    countAndSay n = String.join (List.map (λ (p: Nat × Nat) => toString p.1 ++ toString p.2) 
                                        (List.zip counts digits)) :=
  sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval count_and_say 1

/-
info: '1211'
-/
-- #guard_msgs in
-- #eval count_and_say 4

/-
info: '111221'
-/
-- #guard_msgs in
-- #eval count_and_say 5

-- Apps difficulty: introductory
-- Assurance level: unguarded