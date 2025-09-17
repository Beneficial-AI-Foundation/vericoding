

/-!
{
"name": "dafny_examples_tmp_tmp8qotd4ez_test_shuffle_getRandomDataEntry",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny_examples_tmp_tmp8qotd4ez_test_shuffle_getRandomDataEntry",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Random number generator function translated from Dafny -/
def random (a b : Int) : Int := sorry

/-- Specification for random function -/
theorem random_spec (a b : Int) :
a ≤ b → (a ≤ random a b ∧ random a b ≤ b) := sorry

/-- Convert sequence to set, translated from Dafny -/
def set_of_seq {T} (s : Array T) : List T := sorry

/-- Get random data entry from array avoiding certain values -/
def getRandomDataEntry {T}  (m_workList : Array T) (avoidSet : Array T) : T := sorry

/-- Specification for getRandomDataEntry -/
theorem getRandomDataEntry_spec {T}  (m_workList : Array T) (avoidSet : Array T) :
m_workList.size > 0 →
(∀ x, x ∈ set_of_seq avoidSet → x ∈ set_of_seq m_workList →
getRandomDataEntry m_workList avoidSet ∉ set_of_seq avoidSet) ∧
(∀ x, x ∈ avoidSet → x ∈ m_workList →
getRandomDataEntry m_workList avoidSet ∈ m_workList) := sorry
