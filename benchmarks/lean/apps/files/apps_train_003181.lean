-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 'Get Out Now!'
-/
-- #guard_msgs in
-- #eval outed {"tim": 0, "jim": 2, "randy": 0, "sandy": 7, "andy": 0, "katie": 5, "laura": 1, "saajid": 2, "alex": 3, "john": 2, "mr": 0} "laura"

/-
info: 'Nice Work Champ!'
-/
-- #guard_msgs in
-- #eval outed {"tim": 1, "jim": 3, "randy": 9, "sandy": 6, "andy": 7, "katie": 6, "laura": 9, "saajid": 9, "alex": 9, "john": 9, "mr": 8} "katie"

/-
info: 'Get Out Now!'
-/
-- #guard_msgs in
-- #eval outed {"tim": 2, "jim": 4, "randy": 0, "sandy": 5, "andy": 8, "katie": 6, "laura": 2, "saajid": 2, "alex": 3, "john": 2, "mr": 8} "john"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded