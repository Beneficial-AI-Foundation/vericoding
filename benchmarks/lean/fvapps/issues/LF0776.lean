-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestAlternatingSubarrays (cases: List (List Int)) : List String := sorry

def stringToNat (s: String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_format (cases : List (List Int))
  (h1 : ∀ (l : List Int), List.elem l cases → l.length > 0) : 
  let result := longestAlternatingSubarrays cases
  ∀ (r : String), List.elem r result →
    ∃ nums : List Nat,
    nums.length = (cases.get! (result.indexOf r)).length ∧ 
    ∀ (n : Nat), List.elem n nums → 1 ≤ n ∧ n ≤ (cases.get! (result.indexOf r)).length := sorry

theorem alternating_property (cases : List (List Int))
  (h1 : ∀ (l : List Int), List.elem l cases → l.length > 0) :
  let result := longestAlternatingSubarrays cases
  ∀ (case : List Int) (r : String) (i : Nat),
    List.elem case cases → List.elem r result →
    i < case.length →
    let len := stringToNat (result.get! (cases.indexOf case))
    len > 1 →
    ∀ j, i ≤ j ∧ j < i + len - 1 →
    (case.get! j) * (case.get! (j+1)) < 0 := sorry

theorem identical_elements (cases : List (List Int))
  (h1 : ∀ (l : List Int), List.elem l cases → ∀ (x : Int), List.elem x l → x = 1) :
  let result := longestAlternatingSubarrays cases
  ∀ (case : List Int) (r : String),
    List.elem case cases → List.elem r result →
    r = String.intercalate " " (List.replicate case.length "1") := sorry

theorem alternating_signs (cases : List (List Int))
  (h1 : ∀ (l : List Int), List.elem l cases → l.length ≥ 2)
  (h2 : ∀ (l : List Int), List.elem l cases → ∀ (x : Int), List.elem x l → x ≠ 0) :
  let result := longestAlternatingSubarrays cases
  ∀ (case : List Int) (r : String) (i : Nat),
    List.elem case cases → List.elem r result →
    i < case.length - 1 →
    (case.get! i) * (case.get! (i+1)) < 0 →
    stringToNat ((r.split (· = ' ')).get! i) > 1 := sorry

/-
info: ['1 1 1 1']
-/
-- #guard_msgs in
-- #eval longest_alternating_subarrays [test1]

/-
info: ['4 3 2 1']
-/
-- #guard_msgs in
-- #eval longest_alternating_subarrays [test2]

/-
info: ['1 1 3 2 1 1']
-/
-- #guard_msgs in
-- #eval longest_alternating_subarrays [test3]
-- </vc-theorems>