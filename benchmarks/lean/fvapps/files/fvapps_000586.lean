-- <vc-preamble>
def isLowercaseLetter (c : Char) : Bool := 
  let n := c.toNat
  97 ≤ n && n ≤ 122

def countDescendingPairs (s : List Char) : Nat :=
  match s with
  | [] => 0
  | [_] => 0 
  | x::y::xs => (if x > y then 1 else 0) + countDescendingPairs (y::xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findKDescendingPairs (k : Nat) : List Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_is_k (k : Nat) (k_pos : k > 0) :
  let result := findKDescendingPairs k
  countDescendingPairs result = k :=
sorry

theorem all_lowercase (k : Nat) (k_pos : k > 0) :
  let result := findKDescendingPairs k
  ∀ c ∈ result, isLowercaseLetter c :=
sorry

theorem minimal_length (k : Nat) (k_pos : k > 0) :
  let result := findKDescendingPairs k
  let expected_len := k + 1 + if k > 25 then ((k - 26) / 25) + 1 else 0
  result.length = expected_len :=
sorry

theorem valid_chars (k : Nat) (k_pos : k > 0) :
  let result := findKDescendingPairs k
  ∀ c ∈ result, 97 ≤ c.toNat ∧ c.toNat ≤ 122 := 
sorry
-- </vc-theorems>