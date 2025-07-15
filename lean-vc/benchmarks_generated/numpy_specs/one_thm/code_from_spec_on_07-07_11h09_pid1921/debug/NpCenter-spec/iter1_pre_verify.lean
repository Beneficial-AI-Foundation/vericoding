namespace NpCenter

-- LLM HELPER
def padCenter (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else
    let totalPad := width - s.length
    let leftPad := totalPad / 2
    let rightPad := totalPad - leftPad
    String.mk (List.replicate leftPad ' ') ++ s ++ String.mk (List.replicate rightPad ' ')

def center {n : Nat} (input : Vector String n) (width : Nat) : Vector String n :=
  input.map (fun s => padCenter s width)

-- LLM HELPER
lemma padCenter_length (s : String) (width : Nat) :
  (padCenter s width).length = if s.length >= width then s.length else width := by
  simp [padCenter]
  split_ifs with h
  · rfl
  · simp [String.length_mk, List.length_replicate]
    omega

-- LLM HELPER
lemma padCenter_preserve_long (s : String) (width : Nat) (h : s.length > width) :
  padCenter s width = s := by
  simp [padCenter]
  split_ifs with h'
  · rfl
  · omega

-- LLM HELPER
lemma padCenter_center_property (s : String) (width : Nat) (h : s.length < width) :
  let startPos := (width - s.length + 1) / 2
  let endPos := startPos + s.length - 1
  (padCenter s width).toList.drop startPos |>.take s.length = s.toList := by
  simp [padCenter]
  split_ifs with h'
  · omega
  · simp [String.toList_mk, List.drop_append_of_le_length, List.take_append_of_le_length]
    · simp [List.length_replicate]
      let totalPad := width - s.length
      let leftPad := totalPad / 2
      have : leftPad ≤ (width - s.length + 1) / 2 := by
        simp [leftPad]
        omega
      have : (width - s.length + 1) / 2 ≤ leftPad + 1 := by
        simp [leftPad]
        omega
      cases' Nat.le_total leftPad ((width - s.length + 1) / 2) with h1 h2
      · cases' Nat.eq_or_lt_of_le h1 with h3 h4
        · rw [h3]
          simp [List.drop_replicate]
        · have : (width - s.length + 1) / 2 ≤ leftPad := by
            simp [leftPad]
            have : (width - s.length + 1) / 2 ≤ (width - s.length) / 2 := by
              apply Nat.div_le_div_right
              omega
            exact this
          omega
      · simp [List.drop_replicate]
        have : (width - s.length + 1) / 2 - leftPad ≤ 1 := by
          simp [leftPad]
          omega
        cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (Nat.lt_succ_of_le this)) with h3 h4
        · cases h3 with
          | zero => simp
          | succ n => 
            have : n = 0 := by omega
            simp [this]
        · simp [h4]

theorem center_spec {n : Nat} (input : Vector String n) (width : Nat)
  (h : ∀ i : Fin n, input[i].length ≥ 1) :
  let res := center input width
  (res.toList.length = n) ∧
  (∀ i : Fin n, if input[i].length > width then res[i].length = input[i].length else res[i].length = width) ∧
  (∀ i : Fin n, if input[i].length < width then
    let startPos := (width - input[i].length + 1) / 2
    let endPos := startPos + input[i].length - 1
    res[i].toList.drop startPos |>.take input[i].length = input[i].toList else True) := by
  simp [center]
  constructor
  · simp [Vector.toList_map, List.length_map]
  constructor
  · intro i
    simp [Vector.get_map, padCenter_length]
    split_ifs with h1
    · rfl
    · rfl
  · intro i
    simp [Vector.get_map]
    split_ifs with h1
    · exact padCenter_center_property (input[i]) width h1
    · trivial

end NpCenter