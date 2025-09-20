-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitString (s : String) (sep : String) : List String :=
sorry

def containsString (s : String) (sub : String) : Bool :=
sorry

def startsWithString (s : String) (pre : String) : Bool :=
sorry

def simplify (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem simplify_zero :
  simplify 0 = "" :=
sorry

theorem simplify_format_valid (n : Nat) (h : n > 0) :
  let terms := splitString (simplify n) "+"
  terms.length > 0 :=
sorry

theorem simplify_terms_valid (n : Nat) (h : n > 0) :
  let terms := splitString (simplify n) "+"
  ∀ t ∈ terms,
    (containsString t "*" ∧
     let parts := splitString t "*"
     parts.length = 2 ∧
     let digit := parts[0]!
     let power := parts[1]!
     startsWithString power "10" ∧
     let digitNum := digit.toNat!
     1 ≤ digitNum ∧ digitNum ≤ 9)
    ∨
    (¬containsString t "*" ∧
     t.all Char.isDigit ∧
     let termNum := t.toNat!
     1 ≤ termNum ∧ termNum ≤ 9) :=
sorry

theorem simplify_sums_to_input (n : Nat) :
  let terms := splitString (simplify n) "+"
  terms.foldl
    (fun acc t =>
      if containsString t "*" then
        let parts := splitString t "*"
        acc + parts[0]!.toNat! * parts[1]!.toNat!
      else
        acc + t.toNat!)
    0
  = n :=
sorry

theorem simplify_no_leading_zeros (n : Nat) (h : n > 0) :
  let terms := splitString (simplify n) "+"
  ∀ t ∈ terms, ¬startsWithString t "0" :=
sorry
-- </vc-theorems>