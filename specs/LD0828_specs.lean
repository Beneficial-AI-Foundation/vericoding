-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def random (a b : Int) : Int :=
sorry

def set_of_seq {T} (s : Array T) : List T :=
sorry

def getRandomDataEntry {T}  (m_workList : Array T) (avoidSet : Array T) : T :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem random_spec (a b : Int) :
a ≤ b → (a ≤ random a b ∧ random a b ≤ b) :=
sorry

theorem getRandomDataEntry_spec {T}  (m_workList : Array T) (avoidSet : Array T) :
m_workList.size > 0 →
(∀ x, x ∈ set_of_seq avoidSet → x ∈ set_of_seq m_workList →
getRandomDataEntry m_workList avoidSet ∉ set_of_seq avoidSet) ∧
(∀ x, x ∈ avoidSet → x ∈ m_workList →
getRandomDataEntry m_workList avoidSet ∈ m_workList) :=
sorry
-- </vc-theorems>