-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeater (s : String) (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeater_length (s : String) (n : Nat) :
  (repeater s n).length = s.length * n :=
sorry

theorem repeater_eq_concat (s : String) (n : Nat) :
  repeater s n = String.join (List.replicate n s) :=
sorry

theorem repeater_validity (s : String) (n : Nat) (h : n > 0) :
  ∀ k : Nat, k < n → String.isPrefixOf s (repeater s n) :=
sorry

theorem repeater_zero (s : String) :
  repeater s 0 = "" :=
sorry

theorem repeater_one (s : String) :
  repeater s 1 = s :=
sorry
-- </vc-theorems>