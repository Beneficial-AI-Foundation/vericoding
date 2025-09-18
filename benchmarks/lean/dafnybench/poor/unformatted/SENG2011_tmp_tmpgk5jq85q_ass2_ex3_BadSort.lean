

/-!
{
"name": "SENG2011_tmp_tmpgk5jq85q_ass2_ex3_BadSort",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: SENG2011_tmp_tmpgk5jq85q_ass2_ex3_BadSort",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Predicate that checks if a string is sorted with all b's before all a's which are before all d's
-/
def sortedbad (s : String) : Prop :=
(∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'b' ∧ (s.get ⟨j⟩ = 'a' ∨ s.get ⟨j⟩ = 'd') → i < j) ∧
(∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'a' ∧ s.get ⟨j⟩ = 'b' → i > j) ∧
(∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'a' ∧ s.get ⟨j⟩ = 'd' → i < j) ∧
(∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'd' ∧ (s.get ⟨j⟩ = 'a' ∨ s.get ⟨j⟩ = 'b') → i > j)

/--
BadSort function that takes a string and returns a sorted version according to sortedbad predicate
-/
def BadSort (a : String) : String := sorry

/--
Specification for BadSort function
-/
theorem BadSort_spec (a : String) :
(∀ k, 0 ≤ k ∧ k < a.length → (a.get ⟨k⟩ = 'b' ∨ a.get ⟨k⟩ = 'a' ∨ a.get ⟨k⟩ = 'd')) →
let b := BadSort a
sortedbad b ∧
b.length = a.length := sorry
