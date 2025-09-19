-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeatedStringMatch (a b : String) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_b_returns_valid_result (a : String)
  (h : a.length > 0) :
  repeatedStringMatch a "" = 1 :=
  sorry

theorem result_is_valid_range (a b : String) :
  let r := repeatedStringMatch a b
  r = -1 ∨ r > 0 :=
  sorry

theorem identical_strings (s : String)
  (h : s.length > 0) :
  repeatedStringMatch s s = 1 :=
  sorry

theorem character_set_property (a b : String)
  (ha : a.length > 0)
  (hb : b.length > 0)
  (h : ¬∀c, c ∈ b.data → c ∈ a.data) :
  repeatedStringMatch a b = -1 :=
  sorry

theorem concatenated_copies (s : String)
  (h : s.length > 0) :
  let n := 3
  let b := String.join (List.replicate n s)
  repeatedStringMatch s b ≤ n + 1 :=
  sorry

theorem periodic_property (s : String) (n : Nat)
  (h : s.length > 0)
  (hn : 1 ≤ n ∧ n ≤ 10) :
  let b := String.join (List.replicate n s)
  repeatedStringMatch s b ≤ n :=
  sorry
-- </vc-theorems>