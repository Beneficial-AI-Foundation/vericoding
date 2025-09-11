-- <vc-preamble>
def get_digits (n : Nat) : List Nat := sorry

def is_narc (n : Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_narcissistic : List String → Bool := sorry

theorem get_digits_correct (n : Nat) : 
  get_digits n = (toString n).toList.map (fun c => c.toString.toNat!) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_narc_sum_pow_digits (n : Nat) :
  is_narc n = (n = ((get_digits n).map (fun d => d ^ (get_digits n).length)).foldl (· + ·) 0) := sorry

theorem is_narcissistic_all (values : List String) :
  is_narcissistic values = values.all (fun x => 
    if let some n := x.toNat? then
      is_narc n
    else  
      false) := sorry

theorem non_numeric_returns_false (s : String) : 
  ¬s.all Char.isDigit → ¬is_narcissistic [s] := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_narcissistic 11

/-
info: True
-/
-- #guard_msgs in
-- #eval is_narcissistic "4" 7 "9"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_narcissistic 407 8208
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded