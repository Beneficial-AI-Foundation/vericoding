-- <vc-preamble>
def abs (n : Nat) (m : Nat) : Nat :=
  if n ≥ m then n - m else m - n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_fireworks (n m d : Nat) (fireworks : List (Nat × Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fireworks_total_balls_bound {n m d : Nat} {fireworks : List (Nat × Nat × Nat)}
  (h1 : m > 0) (h2 : n > 0) (h3 : d > 0) :
  solve_fireworks n m d fireworks ≤ (fireworks.foldl (fun acc p => acc + p.2.1) 0) + n :=
sorry

theorem fireworks_timestamps_increasing {n m d : Nat} {fireworks : List (Nat × Nat × Nat)}
  (h1 : m > 0) (h2 : n > 0) (h3 : d > 0) :
  ∀ i, i < fireworks.length - 1 →
    (fireworks.get ⟨i, sorry⟩).2.2 < (fireworks.get ⟨i+1, sorry⟩).2.2 :=
sorry

theorem fireworks_positions_valid {n m d : Nat} {fireworks : List (Nat × Nat × Nat)}
  (h1 : m > 0) (h2 : n > 0) (h3 : d > 0) :
  ∀ f ∈ fireworks, 1 ≤ f.1 ∧ f.1 ≤ n :=
sorry

theorem single_firework_result {n balls d : Nat} {pos : Nat}
  (h1 : n > 0) (h2 : balls > 0) (h3 : d > 0) (h4 : pos = n/2) :
  solve_fireworks n 1 d [(pos, balls, 1)] =
    balls - (List.range n).foldl (fun m i => min m (abs pos (i + 1))) (abs pos 1) :=
sorry
-- </vc-theorems>