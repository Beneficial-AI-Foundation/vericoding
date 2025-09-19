-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findLongest (s : String) : Nat :=
  sorry

def isValidParens (s : String) : Bool :=
  sorry

def substringFromTo (s : String) (i j : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findLongest_valid (s : String) :
  let result := findLongest s
  result ≤ s.length ∧
  result % 2 = 0 :=
sorry

theorem findLongest_optimal (s : String) :
  let result := findLongest s
  ∀ i j, i < s.length → j ≤ s.length → j > i →
    let substr := substringFromTo s i j
    isValidParens substr → substr.length ≤ result :=
sorry

theorem findLongest_exists (s : String) :
  let result := findLongest s
  result > 0 →
  ∃ i j, i < s.length ∧ j ≤ s.length ∧ j > i ∧
    let substr := substringFromTo s i j
    substr.length = result ∧
    isValidParens substr :=
sorry

theorem findLongest_matched_pairs (n : Nat) :
  let s := String.mk (List.replicate n '(' ++ List.replicate n ')')
  findLongest s = 2 * n :=
sorry

theorem findLongest_unmatched_surround (n : Nat) :
  n > 0 →
  let balanced := String.mk (List.replicate n '(' ++ List.replicate n ')')
  let s := ")" ++ balanced ++ "("
  findLongest s = 2 * n :=
sorry
-- </vc-theorems>