-- <vc-preamble>
def isBinaryChar (c : Char) : Bool :=
  c = '0' || c = '1'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringInList (s : String) (l : List String) : Bool := sorry

def find_median_binary_string (n m : Nat) (removed : List String) : String :=
sorry

def isAllZeros (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_median_binary_string_length_matches_input
  {n m : Nat} {removed : List String}
  (h₁ : n < 2^m)
  (h₂ : n = removed.length) :
  (find_median_binary_string n m removed).length = m :=
sorry

theorem find_median_binary_string_binary_chars
  {n m : Nat} {removed : List String}
  (h₁ : n < 2^m)
  (h₂ : n = removed.length) :
  ∀ c, c ∈ (find_median_binary_string n m removed).data → isBinaryChar c :=
sorry

theorem find_median_binary_string_not_in_removed
  {n m : Nat} {removed : List String}
  (h₁ : n < 2^m)
  (h₂ : n = removed.length) :
  stringInList (find_median_binary_string n m removed) removed = false :=
sorry

theorem find_median_binary_string_minimal_case
  {m : Nat} (h : m > 0) :
  let zeros := String.mk (List.replicate m '0')
  let result := find_median_binary_string 1 m [zeros]
  (result.length = m) ∧ (isAllZeros result = false) :=
sorry
-- </vc-theorems>