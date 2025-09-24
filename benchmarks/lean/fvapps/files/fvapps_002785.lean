-- <vc-preamble>
def listSum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => x + listSum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_strings (arr : List String) : List String :=
  sorry

def String.reverse (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_strings_length_preserved (arr : List String)
  (h : ∀ s ∈ arr, s.length > 0) :
  let result := reverse_strings arr
  (result.length = arr.length) ∧
  (∀ i, i < arr.length → (result.get ⟨i, sorry⟩).length = (arr.get ⟨i, sorry⟩).length) :=
sorry

theorem reverse_strings_is_reversible (arr : List String)
  (h : ∀ s ∈ arr, s.length > 0) :
  reverse_strings (reverse_strings arr) = arr :=
sorry

theorem reverse_strings_total_chars_preserved (arr : List String)
  (h : ∀ s ∈ arr, s.length > 0) :
  let result := reverse_strings arr
  (listSum (arr.map String.length)) = (listSum (result.map String.length)) ∧
  String.reverse (String.join arr) = String.join result :=
sorry

theorem reverse_strings_single_char (arr : List String)
  (h : ∀ s ∈ arr, s.length = 1) :
  String.join (reverse_strings arr) = String.reverse (String.join arr) :=
sorry
-- </vc-theorems>