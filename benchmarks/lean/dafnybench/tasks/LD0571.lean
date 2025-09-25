-- <vc-preamble>
partial def palindromic (s : String) (i j : Int) : Prop :=
(0 ≤ i) ∧ (i ≤ j) ∧ (j ≤ s.length) ∧
((j - i < 2) ∨ (s.get ⟨i.toNat⟩ = s.get ⟨(j-1).toNat⟩ ∧ palindromic s (i+1) (j-1)))

def abs (x : Int) : Int :=
if x ≥ 0 then x else -x

def max_interval_for_same_center (s : String) (k lo hi : Int) : Prop :=
(0 ≤ lo) ∧ (lo ≤ hi) ∧ (hi ≤ s.length) ∧
(lo + hi = k) ∧
palindromic s lo hi ∧
(∀ i j, (0 ≤ i) ∧ (i ≤ j) ∧ (j ≤ s.length) ∧ palindromic s i j ∧ (i + j = k) → (j - i ≤ hi - lo))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def expand_from_center (s : String) (i0 j0 : Int) : (Int × Int) :=
sorry

def insert_bogus_chars (s : String) (bogus : Char) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem expand_from_center_spec (s : String) (i0 j0 : Int) :
(0 ≤ i0) ∧ (i0 ≤ j0) ∧ (j0 ≤ s.length) ∧ palindromic s i0 j0 →
let (lo, hi) := expand_from_center s i0 j0
(0 ≤ lo) ∧ (lo ≤ hi) ∧ (hi ≤ s.length) ∧ palindromic s lo hi ∧
(∀ i j, (0 ≤ i) ∧ (i ≤ j) ∧ (j ≤ s.length) ∧ palindromic s i j ∧ (i + j = i0 + j0) →
(j - i ≤ hi - lo)) :=
sorry

theorem insert_bogus_chars_spec (s : String) (bogus : Char) :
let s' := insert_bogus_chars s bogus
(s'.length = 2 * s.length + 1) ∧
(∀ i, (0 ≤ i) ∧ (i ≤ s.length) → s'.get ⟨i * 2⟩  = bogus) ∧
(∀ i, (0 ≤ i) ∧ (i < s.length) → s'.get ⟨i * 2 + 1⟩  = s.get ⟨i⟩) :=
sorry
-- </vc-theorems>