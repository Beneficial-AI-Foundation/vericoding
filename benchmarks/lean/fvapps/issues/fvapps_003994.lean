-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_info {α : Type} (lst : List α) : Result := sorry

theorem array_info_empty (lst : List α) : 
  lst = [] → array_info lst = .Msg "Nothing in the array!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_info_nonempty_structure (lst : List α) :
  lst ≠ [] →
  ∃ result : List (List Nat),
    array_info lst = .Nums result ∧
    result.length = 5 ∧ 
    ∀ x ∈ result, ∃ y, x = [y] := sorry

theorem array_info_length (lst : List α) :
  lst ≠ [] →
  ∃ result : List (List Nat),
    array_info lst = .Nums result ∧
    result.get! 0 = [lst.length] := sorry

theorem array_info_all_ints (lst : List Int) :
  lst ≠ [] →
  ∃ result : List (List Nat),
    array_info lst = .Nums result ∧
    result.get! 1 = [lst.length] ∧
    result.get! 2 = [0] ∧
    result.get! 3 = [0] ∧
    result.get! 4 = [0] := sorry

theorem array_info_all_spaces (lst : List String) :
  lst ≠ [] →
  (∀ s ∈ lst, s.all Char.isWhitespace) →
  ∃ result : List (List Nat),
    array_info lst = .Nums result ∧
    result.get! 1 = [0] ∧
    result.get! 2 = [0] ∧
    result.get! 3 = [0] ∧
    result.get! 4 = [lst.length] := sorry
-- </vc-theorems>