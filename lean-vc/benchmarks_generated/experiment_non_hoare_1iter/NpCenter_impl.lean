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
    let leftPad := (padding + 1) / 2
    let rightPad := padding - leftPad
    String.mk (List.replicate leftPad ' ') ++ s ++ String.mk (List.replicate rightPad ' ')

/-- Center strings within a specified width -/
def center {n : Nat} (input : Vector String n) (width : Nat) : Vector String n := 
  Vector.map (fun s => padString s width) input

-- LLM HELPER
theorem vector_map_length {α β : Type*} {n : Nat} (v : Vector α n) (f : α → β) :
  (Vector.map f v).toList.length = n := by
  simp [Vector.map, Vector.toList]

-- LLM HELPER
theorem padString_length (s : String) (width : Nat) :
  (padString s width).length = if s.length >= width then s.length else width := by
  simp [padString]
  split_ifs with h
  · simp
  · simp [String.length_mk, String.length_append]
    have : s.length < width := Nat.lt_of_not_ge h
    let padding := width - s.length
    let leftPad := (padding + 1) / 2
    let rightPad := padding - leftPad
    have leftPad_rightPad : leftPad + rightPad = padding := by
      simp [leftPad, rightPad]
      omega
    rw [← leftPad_rightPad]
    simp [List.length_replicate]
    omega

-- LLM HELPER
theorem padString_content (s : String) (width : Nat) (h : s.length < width) :
  let startPos := (width - s.length + 1) / 2
  (padString s width).toList.drop startPos |>.take s.length = s.toList := by
  simp [padString, h]
  let padding := width - s.length
  let leftPad := (padding + 1) / 2
  let rightPad := padding - leftPad
  have startPos_eq : startPos = leftPad := by
    simp only [startPos, leftPad]
    congr 1
    exact Nat.add_sub_cancel' (Nat.le_of_lt h)
  rw [startPos_eq]
  simp [String.toList_mk, String.toList_append]
  rw [List.drop_append_of_le_length]
  · simp [List.take_append_of_le_length]
  · simp [List.length_replicate]

/-- Specification: The result has the same length as input -/
theorem center_length {n : Nat} (input : Vector String n) (width : Nat)
  (h : ∀ i : Fin n, input[i].length ≥ 1) :
  let res := center input width
  res.toList.length = n := by
  simp [center]
  exact vector_map_length input (fun s => padString s width)

/-- Specification: Result strings have correct length -/
theorem center_string_length {n : Nat} (input : Vector String n) (width : Nat)
  (h : ∀ i : Fin n, input[i].length ≥ 1) :
  let res := center input width
  ∀ i : Fin n, if input[i].length > width then res[i].length = input[i].length else res[i].length = width := by
  intro i
  simp [center, Vector.map]
  rw [padString_length]
  split_ifs with h1 h2
  · simp
  · simp
  · simp at h2
    have : input[i].length < width := Nat.lt_of_le_of_ne (Nat.le_of_not_gt h1) h2
    simp [this]
  · simp

/-- Specification: Original string is correctly centered -/
theorem center_content {n : Nat} (input : Vector String n) (width : Nat)
  (h : ∀ i : Fin n, input[i].length ≥ 1) :
  let res := center input width
  ∀ i : Fin n, if input[i].length < width then
    let startPos := (width - input[i].length + 1) / 2
    res[i].toList.drop startPos |>.take input[i].length = input[i].toList else True := by
  intro i
  simp [center, Vector.map]
  split_ifs with h1
  · exact padString_content (input[i]) width h1
  · trivial

end DafnySpecs.NpCenter