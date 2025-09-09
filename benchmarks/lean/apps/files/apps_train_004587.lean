/-
### Background
One way to order a nested (reddit-style) commenting system is by giving each comment a rank. 

Generic comments on a thread start with rank 1 and increment, so the second comment on a thread would have rank 2. A reply to comment 1 will be ranked 1.1, and a reply to comment 1.1 will be ranked 1.1.1 . The second comment to reply to comment 1 would be ranked 1.2 .

Note that since 1.1.1 is a valid rank, the ranks given are of type string.   

### Task: 
Given a list of comment ranks (strings), order them as a comment thread would appear 

### Assumptions:  
* there will always be a rank 1 in the given input
* ranks are of type string
* rank numbers are incremented, and not skippped (1.1 could be followed by 1.2, not 1.3)

### Example order:
```
[
  '1',
  '1.1',
  '1.2',
  '1.2.1',
  '2',
  '3',
  '3.1',
  '3.1.1',
  '3.2'
]
```
-/

def sort_ranks (ranks: List String) : List String := sorry

def is_valid_version (s: String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def loose_version_le (v1 v2: String) : Bool := sorry

theorem sort_ranks_maintains_elements (ranks: List String) 
  (h: ∀ x ∈ ranks, is_valid_version x) :
  let sorted := sort_ranks ranks
  ∀ x, (x ∈ ranks ↔ x ∈ sorted) ∧
  sorted.length = ranks.length := sorry

theorem sort_ranks_ordering (ranks: List String)
  (h1: ranks.length ≥ 2)
  (h2: ∀ x ∈ ranks, is_valid_version x) :
  let sorted := sort_ranks ranks
  ∀ (i: Nat) (h: i + 1 < sorted.length),
    loose_version_le (sorted[i]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt h)))
                    (sorted[i+1]'h) := sorry

theorem sort_ranks_idempotent (ranks: List String)
  (h: ∀ x ∈ ranks, is_valid_version x) :
  sort_ranks (sort_ranks ranks) = sort_ranks ranks := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval sort_ranks ["2", "1", "1.1"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval sort_ranks ["3.1", "1", "1.1", "2", "3", "1.2", "3.2", "1.2.1", "3.1.1"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval sort_ranks ["3", "2", "1"]

-- Apps difficulty: introductory
-- Assurance level: unguarded