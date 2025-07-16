def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  l.length = result.length ∧
  let even_idx := (List.range l.length).filter (λ i => i % 2 = 0);
  let even_val_in_result := even_idx.map (λ i => result[i]!);
  let even_val := even_idx.map (λ i => l[i]!);
  (∀ i, i < l.length → (i % 2 ≠ 0 → l[i]! = result[i]!)) ∧
  even_val_in_result.Sorted (· ≤ ·) ∧
  even_val.all (λ x => even_val_in_result.count x = even_val.count x);
-- program termination
∃ result, implementation l = result ∧
spec result

-- LLM HELPER
def sortEvenIndices (l: List Int) : List Int :=
  let n := l.length
  let even_indices := (List.range n).filter (λ i => i % 2 = 0)
  let even_values := even_indices.map (λ i => l[i]!)
  let sorted_even_values := even_values.mergeSort (· ≤ ·)
  let result := List.range n |>.map (λ i =>
    if i % 2 = 0 then
      let pos := even_indices.idxOf i
      sorted_even_values[pos]!
    else
      l[i]!
  )
  result

def implementation (l: List Int) : List Int := sortEvenIndices l

-- LLM HELPER
lemma length_preserved (l: List Int) : 
  (sortEvenIndices l).length = l.length := by
  unfold sortEvenIndices
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma odd_indices_unchanged (l: List Int) (i: Nat) (h1: i < l.length) (h2: i % 2 ≠ 0) :
  (sortEvenIndices l)[i]! = l[i]! := by
  unfold sortEvenIndices
  simp [List.getElem_map, List.getElem_range]
  rw [if_neg h2]

-- LLM HELPER  
lemma even_values_sorted (l: List Int) :
  let even_idx := (List.range l.length).filter (λ i => i % 2 = 0)
  let even_val_in_result := even_idx.map (λ i => (sortEvenIndices l)[i]!)
  even_val_in_result.Sorted (· ≤ ·) := by
  unfold sortEvenIndices
  simp only [List.getElem_map, List.getElem_range]
  apply List.Sorted.map
  apply List.mergeSort_sorted

-- LLM HELPER
lemma even_values_count_preserved (l: List Int) :
  let even_idx := (List.range l.length).filter (λ i => i % 2 = 0)
  let even_val_in_result := even_idx.map (λ i => (sortEvenIndices l)[i]!)
  let even_val := even_idx.map (λ i => l[i]!)
  even_val.all (λ x => even_val_in_result.count x = even_val.count x) := by
  unfold sortEvenIndices
  simp only [List.getElem_map, List.getElem_range]
  apply List.all_eq_true.mpr
  intro x hx
  simp
  apply List.count_mergeSort

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  unfold problem_spec implementation
  use sortEvenIndices l
  constructor
  · rfl
  · constructor
    · exact length_preserved l
    · constructor
      · intros i h1 h2
        exact odd_indices_unchanged l i h1 h2
      · constructor
        · exact even_values_sorted l
        · exact even_values_count_preserved l