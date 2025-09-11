-- <vc-preamble>
def getDigits (n : Nat) : List Nat := sorry 

/- Function that returns the largest number not exceeding n whose digits are monotone increasing -/

def monotoneIncreasingDigits (n : Nat) : Nat := sorry

/- Helper function to compare Options -/
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def optionLE (a b : Option Nat) : Prop :=
  match a, b with
  | some x, some y => x ≤ y
  | none, _ => True
  | _, none => False

/- For any number n, its monotone increasing digits result will have digits in non-decreasing order
    and will not exceed the original number n -/
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_monotone_increasing (n : Nat) : 
  let result := monotoneIncreasingDigits n
  let digits := getDigits result
  (∀ i j : Nat, i < j → j < digits.length → optionLE (digits[i]?) (digits[j]?)) ∧
  result ≤ n := sorry

/- For any number n, its monotone increasing digits result is maximal - incrementing any digit
    would either make it exceed n or break the monotone increasing property -/

theorem largest_possible_result (n : Nat) :
  let result := monotoneIncreasingDigits n
  let digits := getDigits result
  ∀ i : Nat, i < digits.length →
    let digit := digits[i]?
    match digit with
    | none => True
    | some d => d = 9 ∨
      (let incrementedDigits := digits.set i (d + 1)
       let incrementedNum := incrementedDigits.foldl (fun acc d => acc * 10 + d) 0
       incrementedNum > n ∨
       ¬(∀ j k : Nat, j < k → k < incrementedDigits.length → 
           optionLE (incrementedDigits[j]?) (incrementedDigits[k]?))) := sorry

/- Single digit numbers remain unchanged when applying monotone increasing digits -/

theorem single_digit_unchanged (n : Nat) :
  n < 10 → monotoneIncreasingDigits n = n := sorry

/- Numbers that are already monotone increasing remain unchanged -/

theorem already_monotone_unchanged (n : Nat) :
  let digits := getDigits n
  (∀ i j : Nat, i < j → j < digits.length → optionLE (digits[i]?) (digits[j]?)) →
  monotoneIncreasingDigits n = n := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval monotone_increasing_digits 10

/-
info: 1234
-/
-- #guard_msgs in
-- #eval monotone_increasing_digits 1234

/-
info: 299
-/
-- #guard_msgs in
-- #eval monotone_increasing_digits 332
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded