-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ulamSequence (u0 u1 n : Nat) : List Nat := sorry

theorem ulam_sequence_length (u0 u1 n : Nat) (h1: u0 > 0) (h2: u1 > u0) :
  List.length (ulamSequence u0 u1 n) = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ulam_sequence_first_elements (u0 u1 n : Nat) (h1: u0 > 0) (h2: u1 > u0) (h3: n ≥ 3) :
  ulamSequence u0 u1 n ≠ [] ∧
  (ulamSequence u0 u1 n).get ⟨0, by {rw [ulam_sequence_length u0 u1 n h1 h2]; sorry}⟩ = u0 ∧
  (ulamSequence u0 u1 n).get ⟨1, by {rw [ulam_sequence_length u0 u1 n h1 h2]; sorry}⟩ = u1 := sorry

theorem ulam_sequence_strictly_increasing (u0 u1 n : Nat) (h1: u0 > 0) (h2: u1 > u0) (h3: n ≥ 3) :
  ∀ i : Fin n, i.val + 1 < n →
    let seq := ulamSequence u0 u1 n
    let h_length := ulam_sequence_length u0 u1 n h1 h2
    (seq.get ⟨i.val, by {rw [h_length]; exact i.isLt}⟩) <
    (seq.get ⟨i.val + 1, by {rw [h_length]; sorry}⟩) := sorry

theorem ulam_sequence_third_element (u0 u1 n : Nat) (h1: u0 > 0) (h2: u1 > u0) (h3: n ≥ 3) :
  (ulamSequence u0 u1 n).get ⟨2, by {rw [ulam_sequence_length u0 u1 n h1 h2]; sorry}⟩ = u0 + u1 := sorry

theorem ulam_sequence_unique_sum (u0 u1 n : Nat) (h1: u0 > 0) (h2: u1 > u0) (h3: n ≥ 3) :
  ∀ i : Fin n, 2 ≤ i.val → 
  ∃ (p : Nat × Nat), (∀ q : Nat × Nat,
    let seq := ulamSequence u0 u1 n
    let h_length := ulam_sequence_length u0 u1 n h1 h2
    p.1 < p.2 ∧ 
    p.2 < (seq.get ⟨i.val, by {rw [h_length]; exact i.isLt}⟩) ∧
    p.1 ∈ (List.take i.val seq) ∧ 
    p.2 ∈ (List.take i.val seq) ∧
    p.1 + p.2 = (seq.get ⟨i.val, by {rw [h_length]; exact i.isLt}⟩) ∧
    (q.1 < q.2 ∧ 
     q.2 < (seq.get ⟨i.val, by {rw [h_length]; exact i.isLt}⟩) ∧
     q.1 ∈ (List.take i.val seq) ∧ 
     q.2 ∈ (List.take i.val seq) ∧
     q.1 + q.2 = (seq.get ⟨i.val, by {rw [h_length]; exact i.isLt}⟩) → 
     q = p)) := sorry
-- </vc-theorems>