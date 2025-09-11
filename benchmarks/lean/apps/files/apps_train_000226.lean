-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeKDigits (num : String) (k : Nat) : String := sorry

theorem remove_zero_digits 
  (num : String)
  (h : num.any (fun c => '0' ≤ c ∧ c ≤ '9')) :
  removeKDigits num 0 = 
    if (num.dropWhile (· = '0')).isEmpty 
    then "0" 
    else num.dropWhile (· = '0')
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_all_digits
  (num : String) 
  (h1 : num.any (fun c => '0' ≤ c ∧ c ≤ '9'))
  (h2 : num.length ≤ 10) :
  removeKDigits num num.length = "0"
  := sorry

/-
info: '1219'
-/
-- #guard_msgs in
-- #eval remove_k_digits "1432219" 3

/-
info: '200'
-/
-- #guard_msgs in
-- #eval remove_k_digits "10200" 1

/-
info: '0'
-/
-- #guard_msgs in
-- #eval remove_k_digits "10" 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded