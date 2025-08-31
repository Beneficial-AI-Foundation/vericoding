/- 
function_signature: "def exchange(lst1: list[int], lst2: list[int]) -> str"
docstring: |
    In this problem, you will implement a function that takes two lists of numbers,
    and determines whether it is possible to perform an exchange of elements
    between them to make lst1 a list of only even numbers.
    There is no limit on the number of exchanged elements between lst1 and lst2.
    If it is possible to exchange elements between the lst1 and lst2 to make
    all the elements of lst1 to be even, return "YES".
    Otherwise, return "NO". It is assumed that the input lists will be non-empty.
test_cases:
  - input: ([1, 2, 3, 4], [1, 2, 3, 4])
    expected_output: "YES"
  - input: ([1, 2, 3, 4], [1, 5, 3, 4])
    expected_output: "NO"
-/

import Imports.AllImports
import Std

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst1: List Int) (lst2: List Int) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → List Int → String)
-- inputs
(lst1: List Int)
(lst2: List Int) :=
-- spec
let spec (result : String) :=
  lst1 ≠ [] → lst2 ≠ [] →
  let bool_result := ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
      (i ∈ lst1_idxs →
        -- find the (a, b) in exchange where a = i
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2.get! (lst2_idxs.get! i_idx)))
  (bool_result → result = "YES") ∧
  (result = "NO" → ¬ bool_result) ∧
  (result ≠ "YES" ∧ result ≠ "NO" → False)
-- program termination
∃ result,
  implementation lst1 lst2 = result ∧
  spec result

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation ([1, 2, 3, 4], [1, 2, 3, 4]) = "YES"
-- #test implementation ([1, 2, 3, 4], [1, 5, 3, 4]) = "NO"