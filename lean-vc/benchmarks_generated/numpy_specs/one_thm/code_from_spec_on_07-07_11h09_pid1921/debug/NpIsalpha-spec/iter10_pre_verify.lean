namespace NpIsalpha

-- LLM HELPER
def isCharAlpha (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')

-- LLM HELPER  
def isStringAlpha (s : String) : Bool :=
  s.length > 0 ∧ s.all isCharAlpha

def isAlpha {n : Nat} (input : Vector String n) : Vector Bool n := 
  input.map isStringAlpha

-- LLM HELPER
lemma vector_map_length {α β : Type*} {n : Nat} (v : Vector α n) (f : α → β) :
  (v.map f).toList.length = n := by
  simp [Vector.map, Vector.toList_map]

-- LLM HELPER
lemma vector_map_get {α β : Type*} {n : Nat} (v : Vector α n) (f : α → β) (i : Fin n) :
  (v.map f)[i] = f v[i] := by
  simp [Vector.map, Vector.get]

-- LLM HELPER
lemma string_all_iff_forall (s : String) (p : Char → Bool) :
  s.all p = true ↔ ∀ j : Nat, j < s.length → p (s.get ⟨j⟩) = true := by
  simp [String.all_iff_forall]

-- LLM HELPER
lemma isCharAlpha_iff (c : Char) :
  isCharAlpha c = true ↔ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') := by
  simp [isCharAlpha]

theorem isAlpha_spec {n : Nat} (input : Vector String n) :
  let ret := isAlpha input
  (ret.toList.length = n) ∧
  (∀ i : Fin n, ret[i] = (input[i].length > 0 ∧
    ∀ j : Nat, j < input[i].length →
      let c := input[i].get ⟨j⟩
      ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z'))) := by
  constructor
  · simp [isAlpha]
    exact vector_map_length input isStringAlpha
  · intro i
    simp [isAlpha]
    rw [vector_map_get]
    simp [isStringAlpha]
    constructor
    · intro h
      constructor
      · exact h.1
      · intro j hj
        have : isCharAlpha (input[i].get ⟨j⟩) = true := by
          rw [← string_all_iff_forall] at h
          exact h.2 j hj
        rw [isCharAlpha_iff] at this
        exact this
    · intro h
      constructor
      · exact h.1
      · rw [string_all_iff_forall]
        intro j hj
        rw [isCharAlpha_iff]
        exact h.2 j hj

end NpIsalpha