-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_word_indices (n m : Nat) (group_a group_b : List String) : List String := sorry

def isSortedList (l : List String) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-definitions>

-- <vc-theorems>
theorem find_word_indices_output_properties {n m : Nat} {group_a group_b : List String}
  (hn : 1 ≤ n ∧ n ≤ 100) (hm : 1 ≤ m ∧ m ≤ 100)
  (ha : group_a.length = n) (hb : group_b.length = m)
  (hg : ∀ s ∈ group_a ++ group_b, s.length ≥ 1) :
  let result := find_word_indices n m group_a group_b;
  (result.length = m) ∧ 
  (∀ output ∈ result, 
    output = "-1" ∨
    (let nums := output.split (· = ' ');
     (∀ num ∈ nums, ∃ d : Nat, num.toNat? = some d ∧ 1 ≤ d ∧ d ≤ n) ∧
     isSortedList nums)) := sorry

theorem find_word_indices_correctness {n m : Nat} {group_a group_b : List String}
  (ha : group_a.length = n) (hb : group_b.length = m)
  (hg : ∀ s ∈ group_a ++ group_b, s.length ≥ 1) :
  let result := find_word_indices n m group_a group_b;
  ∀ i < m,
    if group_b[i]! ∈ group_a 
    then 
      result[i]! ≠ "-1" ∧
      ∀ idx ∈ (result[i]!).split (· = ' '),
        (∃ pos : Nat, idx.toNat? = some pos ∧ 
         group_a[pos - 1]! = group_b[i]!)
    else
      result[i]! = "-1" := sorry
-- </vc-theorems>