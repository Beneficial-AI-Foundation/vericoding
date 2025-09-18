-- <vc-preamble>
def abs (x : Int) : Int :=
  if x < 0 then -x else x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximum (l : List Int) : Int :=
sorry

def minimum (l : List Int) : Int :=
sorry

def smallest_distance_pair : List Int → Nat → Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem smallest_distance_pair_properties {nums : List Int} {k : Nat}
    (h1 : nums.length ≥ 2)
    (h2 : k ≥ 1)
    (h3 : k ≤ (nums.length * (nums.length - 1)) / 2)
    (h4 : ∀ x ∈ nums, -100 ≤ x ∧ x ≤ 100) :
    let result := smallest_distance_pair nums k;
    result ≥ 0 ∧
    result ≤ maximum nums - minimum nums :=
sorry

theorem identical_elements {n : List Int} (h : n.length ≥ 2) :
  smallest_distance_pair (List.replicate n.length (n.get! 0)) 1 = 0 :=
sorry

theorem sorted_input_equivalence {nums : List Int} (h : nums.length ≥ 2) :
  smallest_distance_pair nums 1 = smallest_distance_pair (nums.reverse.reverse) 1 :=
sorry
-- </vc-theorems>