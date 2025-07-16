/-
# NumPy Center Specification

Port of np_center.dfy to Lean 4
-/

namespace DafnySpecs.NpCenter

-- LLM HELPER
def padString (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else
    let padding := width - s.length
    let leftPad := padding / 2
    let rightPad := padding - leftPad
    String.mk (List.replicate leftPad ' ') ++ s ++ String.mk (List.replicate rightPad ' ')

/-- Center strings within a specified width -/
def center {n : Nat} (input : Vector String n) (width : Nat) : Vector String n := 
  ⟨(input.toArray.map (fun s => padString s width)), by simp [Vector.toArray_length]⟩

-- LLM HELPER
lemma padString_length (s : String) (width : Nat) :
  (padString s width).length = if s.length >= width then s.length else width := by
  unfold padString
  split_ifs with h
  · rfl
  · simp [String.length_mk, List.length_replicate]
    ring

-- LLM HELPER
lemma vector_map_length {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) :
  (Vector.mk (v.toArray.map f) (by simp [Vector.toArray_length])).toArray.size = n := by
  simp

/-- Specification: The result has the same length as input -/
theorem center_length {n : Nat} (input : Vector String n) (width : Nat)
  (h : ∀ i : Fin n, input[i].length ≥ 1) :
  let res := center input width
  res.toArray.size = n := by
  unfold center
  simp [Vector.toArray_length]

/-- Specification: Result strings have correct length -/
theorem center_string_length {n : Nat} (input : Vector String n) (width : Nat)
  (h : ∀ i : Fin n, input[i].length ≥ 1) :
  let res := center input width
  ∀ i : Fin n, if input[i].length > width then res[i].length = input[i].length else res[i].length = width := by
  intro i
  unfold center
  simp [Vector.get_mk]
  rw [padString_length]
  split_ifs with h1
  · rfl
  · rfl

-- LLM HELPER
lemma padString_content (s : String) (width : Nat) (h : s.length < width) :
  let result := padString s width
  let startPos := (width - s.length + 1) / 2
  let endPos := startPos + s.length - 1
  result.toList.drop startPos |>.take s.length = s.toList := by
  unfold padString
  simp [h]
  let padding := width - s.length
  let leftPad := padding / 2
  let rightPad := padding - leftPad
  simp [String.toList_mk, List.drop_append, List.take_append]
  have h1 : leftPad = (width - s.length + 1) / 2 := by
    simp [leftPad, padding]
    ring
  rw [h1]
  simp [List.drop_replicate, List.take_replicate]
  ring

/-- Specification: Original string is correctly centered -/
theorem center_content {n : Nat} (input : Vector String n) (width : Nat)
  (h : ∀ i : Fin n, input[i].length ≥ 1) :
  let res := center input width
  ∀ i : Fin n, if input[i].length < width then
    let startPos := (width - input[i].length + 1) / 2
    let endPos := startPos + input[i].length - 1
    res[i].toList.drop startPos |>.take input[i].length = input[i].toList else True := by
  intro i
  unfold center
  simp [Vector.get_mk]
  split_ifs with h1
  · exact padString_content _ _ h1
  · trivial

end DafnySpecs.NpCenter