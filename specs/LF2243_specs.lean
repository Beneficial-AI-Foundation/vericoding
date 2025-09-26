-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_loaves (k : Float) : (Nat × List (Nat × Float)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_loaves_result_is_four (k : Float) 
  (hk : 1 ≤ k ∧ k ≤ 10) :
  (max_loaves k).1 = 4 :=
  sorry

theorem max_loaves_gives_three_instructions (k : Float)
  (hk : 1 ≤ k ∧ k ≤ 10) :
  List.length (max_loaves k).2 = 3 :=
  sorry

theorem max_loaves_cut_sum_is_point_nine (k : Float)
  (hk : 1 ≤ k ∧ k ≤ 10) :
  let cuts := (max_loaves k).2;
  let total := (cuts.map (λ x => x.2)).foldl (λ x y => x + y) 0;
  Float.abs (total - 0.9) < 1e-10 :=
  sorry

theorem max_loaves_cuts_are_decreasing (k : Float)
  (hk : 1 ≤ k ∧ k ≤ 10) :
  let cuts := (max_loaves k).2;
  let lengths := cuts.map (λ x => x.2);
  ∀ i : Fin (lengths.length - 1),
    lengths[i] ≥ lengths[i.val + 1] :=
  sorry

theorem max_loaves_indices_are_valid (k : Float)
  (hk : 1 ≤ k ∧ k ≤ 10) :
  let cuts := (max_loaves k).2;
  have h_len : List.length cuts = 3 := by exact max_loaves_gives_three_instructions k hk;
  have h0 : 0 < 3 := by exact Nat.zero_lt_succ 2
  have h1 : 1 < 3 := by exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)
  have h2 : 2 < 3 := by exact Nat.lt_succ_self 2
  have h0' : 0 < List.length cuts := by rw [h_len]; exact h0
  have h1' : 1 < List.length cuts := by rw [h_len]; exact h1
  have h2' : 2 < List.length cuts := by rw [h_len]; exact h2
  (cuts.get ⟨0, h0'⟩).1 = 0 ∧ 
  (cuts.get ⟨1, h1'⟩).1 = 0 ∧
  (cuts.get ⟨2, h2'⟩).1 = 1 :=
  sorry
-- </vc-theorems>