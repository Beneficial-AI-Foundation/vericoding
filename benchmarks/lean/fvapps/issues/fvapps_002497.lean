-- <vc-preamble>
def SetInt.contains (s : SetInt) (x : Int) : Bool :=
  match s with
  | mk list => list.contains x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SetInt.empty : SetInt := SetInt.mk []

def calculate_happiness (arr : List Int) (setA setB : SetInt) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem happiness_count_property (arr : List Int) (setA setB : SetInt) 
    (h : arr.length > 0) :
  calculate_happiness arr setA setB = 
    ((arr.filter (λ x => setA.contains x)).length - 
     (arr.filter (λ x => setB.contains x)).length) :=
  sorry

theorem disjoint_set_no_effect (arr : List Int) (setA : SetInt) 
    (h : arr.length > 0) :
  let disjointSet := SetInt.mk [arr.maximum?.get!.add 1]
  (calculate_happiness arr setA disjointSet = calculate_happiness arr setA SetInt.empty) ∧ 
  (calculate_happiness arr disjointSet setA = calculate_happiness arr SetInt.empty setA) :=
  sorry

theorem empty_sets_zero (arr : List Int) (h : arr.length > 0) :
  calculate_happiness arr SetInt.empty SetInt.empty = 0 :=
  sorry

theorem same_set_cancels (arr : List Int) (testSet : SetInt) 
    (h : arr.length > 0) :
  calculate_happiness arr testSet testSet = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_happiness [1, 5, 3] {3, 1} {5, 7}

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_happiness [1, 2, 3] {4, 5} {6, 7}

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_happiness [1, 1, 2, 2, 3] {1, 3} {2}
-- </vc-theorems>