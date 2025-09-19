-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def avoid_flood (rains : List Nat) : List Int := sorry

theorem avoid_flood_length {rains : List Nat} {result : List Int}
  (h : result = avoid_flood rains) (h_valid : result ≠ []) :
  result.length = rains.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem avoid_flood_rain_days {rains : List Nat} {result : List Int}
  (h : result = avoid_flood rains) (h_valid : result ≠ []) (h_len : result.length = rains.length) :
  ∀ i : Fin rains.length, rains[i] > 0 → result[i] = -1 := sorry

theorem avoid_flood_dry_days {rains : List Nat} {result : List Int}
  (h : result = avoid_flood rains) (h_valid : result ≠ []) (h_len : result.length = rains.length) :
  ∀ i : Fin rains.length, rains[i] = 0 → result[i] > 0 := sorry

theorem avoid_flood_no_flooding {rains : List Nat} {result : List Int}
  (h : result = avoid_flood rains) (h_valid : result ≠ []) (h_len : result.length = rains.length) :
  ∀ i j : Fin rains.length, i.val < j.val →
  rains[i] > 0 → rains[i] = rains[j] →
  ∃ k : Fin rains.length, i.val < k.val ∧ k.val < j.val ∧ rains[k] = 0 ∧ result[k] = rains[i] := sorry

theorem avoid_flood_no_solution_implies_flooding {rains : List Nat} 
  (h : avoid_flood rains = []) :
  ∃ i j : Fin rains.length, i.val < j.val ∧
  rains[i] > 0 ∧ rains[i] = rains[j] ∧
  (∀ k : Fin rains.length, i.val < k.val → k.val < j.val → rains[k] ≠ 0) := sorry

theorem avoid_flood_all_dry {rains : List Nat}
  (h : ∀ i : Fin rains.length, rains[i] = 0) :
  ∀ x ∈ avoid_flood rains, x > 0 := sorry

theorem avoid_flood_all_rain {rains : List Nat}
  (h : ∀ i : Fin rains.length, rains[i] > 0) :
  (∀ i j : Fin rains.length, i.val ≠ j.val → rains[i] ≠ rains[j] → 
    avoid_flood rains = List.replicate rains.length (-1)) ∧
  (∃ i j : Fin rains.length, i.val ≠ j.val ∧ rains[i] = rains[j] → 
    avoid_flood rains = []) := sorry
-- </vc-theorems>