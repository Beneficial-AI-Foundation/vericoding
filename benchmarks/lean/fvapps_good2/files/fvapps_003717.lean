-- <vc-preamble>
def split (s : String) : List String := String.splitOn s "\n"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countCarries (input : String) : String :=
sorry

def carry_count (a b : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_line_carries_correct
  (a b : Nat)
  (h1 : a ≤ 999999)
  (h2 : b ≤ 999999) :
  let result := countCarries s!"{a} {b}"
  let expected :=
    let carry := carry_count a b
    if carry = 0 then "No carry operation"
    else s!"{carry} carry operations"
  result = expected :=
sorry

theorem multiple_lines_carries_length
  {n : Nat}
  (pairs : List (Nat × Nat))
  (h1 : ∀ p : Nat × Nat, p ∈ pairs → (Prod.fst p) ≤ 9999 ∧ (Prod.snd p) ≤ 9999)
  (h2 : pairs.length > 0)
  (h3 : pairs.length ≤ 10) :
  let input := String.intercalate "\n" (pairs.map (λ p => s!"{Prod.fst p} {Prod.snd p}"))
  (split (countCarries input)).length = pairs.length :=
sorry

theorem single_digit_carries_correct
  (a b : Nat)
  (h1 : a ≤ 9)
  (h2 : b ≤ 9) :
  countCarries s!"{a} {b}" =
    if a + b > 9 then "1 carry operations"
    else "No carry operation" :=
sorry
-- </vc-theorems>