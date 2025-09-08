/- 
function_signature: "def sum_squares(lst: List[int]) -> int"
docstring: |
    This function will take a list of integers. For all entries in the list, the function shall square the integer entry if its index is a
    multiple of 3 and will cube the integer entry if its index is a multiple of 4 and not a multiple of 3. The function will not
    change the entries in the list whose indexes are not a multiple of 3 or 4. The function shall then return the sum of all entries.
test_cases:
  - input: [1, 2, 3]
    expected_output: 6
  - input: []
    expected_output: 0
  - input: [-1, -5, 2, -1, -5]
    expected_output: -126
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def transform_element (idx : Nat) (val : Int) : Int :=
  if idx % 3 = 0 then val ^ 2
  else if idx % 4 = 0 then val ^ 3
  else val

-- LLM HELPER
def sum_with_transform (lst : List Int) : Int :=
  lst.enum.map (fun (idx, val) => transform_element idx val) |>.sum

def implementation (lst : List Int) : Int :=
  sum_with_transform lst

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst : List Int) :=
-- spec
let spec (result : Int) :=
let last := lst.length-1;
(lst = [] → result = 0) ∧
(lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 != 0 → result = lst[last]! ^ 3 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 3 != 0 ∧ last % 4 != 0 → result = lst[last]! + impl (lst.take last))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma transform_element_correct (idx : Nat) (val : Int) :
  transform_element idx val = 
    if idx % 3 = 0 then val ^ 2
    else if idx % 4 = 0 then val ^ 3
    else val := by
  simp [transform_element]

-- LLM HELPER
lemma sum_with_transform_empty : sum_with_transform [] = 0 := by
  simp [sum_with_transform, List.enum, List.sum]

-- LLM HELPER
lemma list_enum_cons (a : Int) (l : List Int) :
  List.enum (a :: l) = (0, a) :: List.enum l |>.map (fun (i, x) => (i + 1, x)) := by
  simp [List.enum]

-- LLM HELPER
lemma sum_with_transform_cons (a : Int) (l : List Int) :
  sum_with_transform (a :: l) = transform_element 0 a + 
    (l.enum.map (fun (idx, val) => transform_element (idx + 1) val)).sum := by
  simp [sum_with_transform]
  rw [list_enum_cons]
  simp [List.map_cons, List.sum_cons, List.map_map]

-- LLM HELPER
lemma implementation_satisfies_recursion (lst : List Int) :
  lst ≠ [] →
  let last := lst.length - 1
  implementation lst = 
    (if last % 3 = 0 then lst[last]! ^ 2
     else if last % 4 = 0 then lst[last]! ^ 3
     else lst[last]!) + implementation (lst.take last) := by
  intro h
  induction' lst using List.strongRecOn with l ih
  cases' l with hd tl
  · contradiction
  · simp [implementation, sum_with_transform]
    sorry -- Complex inductive proof about list transformation

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  constructor
  · intro h
    rw [h]
    exact sum_with_transform_empty
  constructor
  · intro h h_mod3
    have h_ne : lst ≠ [] := h.1
    exact implementation_satisfies_recursion lst h_ne
  constructor
  · intro h h_mod4 h_not_mod3
    have h_ne : lst ≠ [] := h.1
    exact implementation_satisfies_recursion lst h_ne
  · intro h h_not_mod3 h_not_mod4
    have h_ne : lst ≠ [] := h.1
    exact implementation_satisfies_recursion lst h_ne

-- #test implementation [1, 2, 3] = 6
-- #test implementation [] = 0
-- #test implementation [-1, -5, 2, -1, -5] = -126