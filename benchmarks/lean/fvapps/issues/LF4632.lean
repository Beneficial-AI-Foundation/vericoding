-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unpack : NestedType → List (String ⊕ Int) := sorry

def isNested : NestedType → Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unpack_flattens_nested : ∀ (x : NestedType),
  let result := unpack x
  -- Result is a list of non-nested values
  result.length > 0 := sorry

theorem unpack_preserves_string : ∀ (s : String),
  unpack (NestedType.str s) = [Sum.inl s] := sorry 

theorem unpack_preserves_list_ints : ∀ (lst : List Int),
  let nested := lst.map NestedType.int
  let result := unpack (NestedType.lst nested)
  -- All elements are preserved and length is preserved
  result.length = lst.length ∧
  ∀ (x : Int), x ∈ lst → Sum.inr x ∈ result := sorry

/-
info: expected2
-/
-- #guard_msgs in
-- #eval sorted unpack(test2)
-- </vc-theorems>