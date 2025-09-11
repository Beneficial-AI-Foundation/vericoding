-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def head_smash (arr : List String) : List String ⊕ String := sorry

theorem head_smash_empty : 
  head_smash [] = Sum.inr "Gym is empty" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem head_smash_nonempty_properties {arr : List String} (h : arr ≠ []) :
  match head_smash arr with
  | Sum.inl result => 
      -- Same length as input
      result.length = arr.length ∧  
      -- Each string in result has same length as corresponding input
      (∀ i, i < result.length → (result.get ⟨i, by sorry⟩).length = (arr.get ⟨i, by sorry⟩).length) ∧
      -- No O characters in result
      (∀ s ∈ result, ∀ c ∈ s.data, c ≠ 'O') ∧
      -- Only O characters were replaced with spaces
      (∀ i < result.length, ∀ j < (result.get ⟨i, by sorry⟩).length,
        (let orig := (arr.get ⟨i, by sorry⟩).data.get ⟨j, by sorry⟩;
         let transformed := (result.get ⟨i, by sorry⟩).data.get ⟨j, by sorry⟩;
         orig = transformed ∨ (orig = 'O' ∧ transformed = ' ')))
  | Sum.inr _ => False
  := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval head_smash ["*****************************************", "**  _O_   *   _O_   *   _O_   *   _O_  **", "** /(.)J  *  C(.)J  *  /(.)J  *  C(.)J **", "** _| |_  *  _| |_  *  _( )_  *  _( )_ *"]

/-
info: 'Gym is empty'
-/
-- #guard_msgs in
-- #eval head_smash []

/-
info: "This isn't the gym!!"
-/
-- #guard_msgs in
-- #eval head_smash 876
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded