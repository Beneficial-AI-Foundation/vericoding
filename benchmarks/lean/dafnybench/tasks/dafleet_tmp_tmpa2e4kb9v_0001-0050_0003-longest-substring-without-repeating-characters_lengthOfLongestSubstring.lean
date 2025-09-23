-- <vc-preamble>
structure Interval where
left : Int
right : Int
valid : left ≤ right

def length (iv : Interval) : Int :=
iv.right - iv.left

def valid_interval (s : String) (iv : Interval) : Prop :=
(0 ≤ iv.left ∧ iv.left ≤ iv.right ∧ iv.right ≤ s.length) ∧
(∀ i j, iv.left ≤ i ∧ i < j ∧ j < iv.right → s.get ⟨i.toNat⟩ ≠ s.get ⟨j.toNat⟩)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lengthOfLongestSubstring (s : String) : Int × Interval :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lengthOfLongestSubstring_spec (s : String) :
let result := lengthOfLongestSubstring s
let n := result.1
let best_iv := result.2
valid_interval s best_iv ∧
length best_iv = n ∧
(∀ iv : Interval, valid_interval s iv → length iv ≤ n) :=
sorry
-- </vc-theorems>