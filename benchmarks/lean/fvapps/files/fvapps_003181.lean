-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def outed (meet : Array (String × Nat)) (boss : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem outed_result_valid (meet : Array (String × Nat)) (boss : String) :
  (outed meet boss = "Get Out Now!") ∨ (outed meet boss = "Nice Work Champ!") :=
  sorry

theorem outed_avg_determines_result (meet : Array (String × Nat)) (boss : String) :
  let total := (meet.map (fun x => x.2)).foldl (· + ·) 0
  let avg := total / meet.size
  (avg > 5 → outed meet boss = "Nice Work Champ!") ∧
  (avg ≤ 5 → outed meet boss = "Get Out Now!") :=
  sorry

theorem outed_all_happy (meet : Array (String × Nat)) (boss : String) 
  (h : ∀ x ∈ meet, x.2 = 10) :
  outed meet boss = "Nice Work Champ!" :=
  sorry

theorem outed_all_unhappy (meet : Array (String × Nat)) (boss : String)
  (h : ∀ x ∈ meet, x.2 = 0) :
  outed meet boss = "Get Out Now!" :=
  sorry
-- </vc-theorems>