-- <vc-preamble>
partial def palindromic (s : String) (i j : Int) : Prop :=
(0 ≤ i) ∧ (i ≤ j) ∧ (j ≤ s.length) ∧
(j - i < 2 ∨ (s.get ⟨i.toNat⟩ = s.get ⟨ (j-1).toNat⟩  ∧ palindromic s (i+1) (j-1)))

def inbound_radius (s : String) (c r : Int) : Prop :=
r ≥ 0 ∧ 0 ≤ c-r ∧ c+r < s.length

def palindromic_radius (s : String) (c r : Int) : Prop :=
inbound_radius s c r → palindromic s (c-r) (c+r+1)

def max_radius (s : String) (c r : Int) : Prop :=
inbound_radius s c r ∧
palindromic_radius s c r ∧
(∀ r', r' > r ∧ inbound_radius s c r' → ¬palindromic_radius s c r')

def abs (x : Int) : Int :=
if x ≥ 0 then x else -x

def max_interval_for_same_center (s : String) (k lo hi : Int) : Prop :=
(0 ≤ lo) ∧ (lo ≤ hi) ∧ (hi ≤ s.length) ∧
lo + hi = k ∧
palindromic s lo hi ∧
(∀ i j, (0 ≤ i) ∧ (i ≤ j) ∧ (j ≤ s.length) ∧
palindromic s i j ∧ i + j = k → j - i ≤ hi - lo)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def expand_from_center (s : String) (i0 j0 : Int) : (Int × Int) :=
sorry

def insert_bogus_chars (s : String) (bogus : Char) : String :=
sorry

def argmax (a : Array Int) (start : Int) : (Int × Int) :=
sorry

def longestPalindrome (s : String) : (String × Int × Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem expand_from_center_spec (s : String) (i0 j0 : Int) :
(0 ≤ i0) ∧ (i0 ≤ j0) ∧ (j0 ≤ s.length) ∧ palindromic s i0 j0 →
let (lo, hi) := expand_from_center s i0 j0
(0 ≤ lo) ∧ (lo ≤ hi) ∧ (hi ≤ s.length) ∧ palindromic s lo hi ∧
(∀ i j, (0 ≤ i) ∧ (i ≤ j) ∧ (j ≤ s.length) ∧ palindromic s i j ∧
(i + j = i0 + j0) → (j - i ≤ hi - lo)) :=
sorry

theorem longestPalindrome_spec (s : String) :
let (ans, lo, hi) := longestPalindrome s
(0 ≤ lo) ∧ (lo ≤ hi) ∧ (hi ≤ s.length) ∧
(ans = s.extract ⟨lo.toNat⟩  ⟨hi.toNat⟩ ) ∧
palindromic s lo hi ∧
(∀ i j, (0 ≤ i) ∧ (i ≤ j) ∧ (j ≤ s.length) ∧
palindromic s i j → j - i ≤ hi - lo) :=
sorry
-- </vc-theorems>