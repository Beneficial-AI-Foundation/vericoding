-- <vc-preamble>
def highest_age (persons1 persons2 : List Person) : Option String := sorry

theorem highest_age_empty_lists : 
  highest_age [] [] = none := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total_age_for_name (persons : List Person) (name : String) : Nat :=
  (persons.filter (fun p => p.name = name)).foldl (fun acc p => acc + p.age) 0
-- </vc-definitions>

-- <vc-theorems>
theorem highest_age_in_input (persons1 persons2 : List Person) (result : String) :
  highest_age persons1 persons2 = some result →
  ∃ p, p ∈ persons1 ++ persons2 ∧ p.name = result := sorry

theorem highest_age_has_max_total (persons1 persons2 : List Person) (result : String) :
  highest_age persons1 persons2 = some result →
  ∀ p ∈ persons1 ++ persons2,
    total_age_for_name (persons1 ++ persons2) p.name ≤ 
    total_age_for_name (persons1 ++ persons2) result := sorry

theorem highest_age_lexicographically_first (persons1 persons2 : List Person) (result : String) :
  highest_age persons1 persons2 = some result →
  let persons := persons1 ++ persons2
  ∀ p ∈ persons,
    (total_age_for_name persons p.name = total_age_for_name persons result → result ≤ p.name) := sorry

theorem highest_age_deterministic (persons1 persons2 : List Person) :
  highest_age persons1 persons2 = highest_age persons1 persons2 := sorry

theorem highest_age_order_independent (persons1 persons2 p1 p2 : List Person) :
  persons1.length = p1.length →
  persons2.length = p2.length →
  (∀ p, p ∈ persons1 ↔ p ∈ p1) →
  (∀ p, p ∈ persons2 ↔ p ∈ p2) →
  highest_age persons1 persons2 = highest_age p1 p2 := sorry

/-
info: 'alice'
-/
-- #guard_msgs in
-- #eval highest_age [{"name": "kay", "age": 1}, {"name": "john", "age": 13}, {"name": "kay", "age": 76}] [{"name": "john", "age": 1}, {"name": "alice", "age": 77}]

/-
info: 'kay'
-/
-- #guard_msgs in
-- #eval highest_age [{"name": "kay", "age": 1}, {"name": "john", "age": 13}, {"name": "kay", "age": 76}] [{"name": "john", "age": 1}, {"name": "alice", "age": 76}]

/-
info: 'kay'
-/
-- #guard_msgs in
-- #eval highest_age [{"name": "kay", "age": 2}, {"name": "john", "age": 130}, {"name": "kay", "age": 130}] [{"name": "john", "age": 1}, {"name": "alice", "age": 76}]
-- </vc-theorems>