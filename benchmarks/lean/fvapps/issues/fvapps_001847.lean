-- <vc-preamble>
def deserialize (s : String) : NestedInteger :=
  sorry

def nestedIntToPython (ni : NestedInteger) : NestedInteger :=
  sorry

def pythonToStr (val : NestedInteger) : String :=
  sorry

def isInteger (ni : NestedInteger) : Bool :=
  match ni with
  | NestedInteger.Integer _ => true
  | _ => false
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getInteger (ni : NestedInteger) : Int :=
  match ni with
  | NestedInteger.Integer n => n
  | _ => 0 -- undefined behavior in this case
-- </vc-definitions>

-- <vc-theorems>
theorem nested_integer_roundtrip (val : NestedInteger) :
  nestedIntToPython (deserialize (pythonToStr val)) = val :=
  sorry

theorem simple_integers_preserve_value (n : Int) (h : -1000 ≤ n ∧ n ≤ 1000) :
  isInteger (deserialize (toString n)) = true ∧
  getInteger (deserialize (toString n)) = n :=
  sorry

theorem flat_lists_preserve_structure (lst : List Int) 
  (h : ∀ x ∈ lst, -1000 ≤ x ∧ x ≤ 1000) :
  nestedIntToPython (deserialize (toString lst)) = 
  NestedInteger.List (lst.map NestedInteger.Integer) :=
  sorry
-- </vc-theorems>