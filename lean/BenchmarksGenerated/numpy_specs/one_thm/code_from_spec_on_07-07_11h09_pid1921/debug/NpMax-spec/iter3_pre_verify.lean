namespace NpMax

-- LLM HELPER
def find_max_helper (a : Vector Int n) (start : Fin n) : Int × Fin n :=
  let rec loop (i : Nat) (acc : Int) (acc_idx : Fin n) : Int × Fin n :=
    if hi : i < n then
      let curr_idx : Fin n := ⟨i, hi⟩
      let curr_val := a[curr_idx]
      if curr_val > acc then
        if i + 1 < n then
          loop (i + 1) curr_val curr_idx
        else
          (curr_val, curr_idx)
      else
        if i + 1 < n then
          loop (i + 1) acc acc_idx
        else
          (acc, acc_idx)
    else
      (acc, acc_idx)
  termination_by n - i
  loop start.val a[start] start

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  let first_idx : Fin n := ⟨0, h⟩
  (find_max_helper a first_idx).1

-- LLM HELPER
lemma max_is_element {n : Nat} (h : n > 0) (a : Vector Int n) : 
  ∃ i : Fin n, max h a = a[i] := by
  use ⟨0, h⟩
  simp [max, find_max_helper]

-- LLM HELPER  
lemma max_is_maximal {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  intro i
  simp [max, find_max_helper]

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  constructor
  · exact max_is_element h a
  · exact max_is_maximal h a

end NpMax