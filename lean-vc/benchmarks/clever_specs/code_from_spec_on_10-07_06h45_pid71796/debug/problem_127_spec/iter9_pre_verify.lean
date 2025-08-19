def problem_spec
(implementation: Int × Int → Int × Int → String)
(interval1: Int × Int)
(interval2: Int × Int) :=
let spec (result: String) :=
let (s1, e1) := interval1;
let (s2, e2) := interval2;
s1 ≤ e1 → s2 ≤ e2 →
let intersectionStart := max s1 s2;
let intersectionEnd := min e1 e2;
let hasIntersection := intersectionStart ≤ intersectionEnd;
let isPrime := Nat.Prime (intersectionEnd - intersectionStart).natAbs;
(result = "YES" ↔ hasIntersection ∧ isPrime) ∧
(result = "NO" ↔ ¬hasIntersection ∨ ¬isPrime) ∧
(result = "YES" ∨ result = "NO")
∃ result, implementation interval1 interval2 = result ∧
spec result

-- LLM HELPER
def hasIntersection (interval1: Int × Int) (interval2: Int × Int) : Bool :=
let (s1, e1) := interval1
let (s2, e2) := interval2
let intersectionStart := max s1 s2
let intersectionEnd := min e1 e2
intersectionStart ≤ intersectionEnd

-- LLM HELPER
def intersectionLength (interval1: Int × Int) (interval2: Int × Int) : Int :=
let (s1, e1) := interval1
let (s2, e2) := interval2
let intersectionStart := max s1 s2
let intersectionEnd := min e1 e2
intersectionEnd - intersectionStart

-- LLM HELPER
def isPrimeLengthIntersection (interval1: Int × Int) (interval2: Int × Int) : Bool :=
if hasIntersection interval1 interval2 then
  let len := intersectionLength interval1 interval2
  if len ≥ 0 then Nat.Prime len.natAbs else false
else false

def implementation (interval1: Int × Int) (interval2: Int × Int) : String :=
let (s1, e1) := interval1
let (s2, e2) := interval2
if s1 > e1 ∨ s2 > e2 then "NO"
else
  let intersectionStart := max s1 s2
  let intersectionEnd := min e1 e2
  let hasInter := intersectionStart ≤ intersectionEnd
  if ¬hasInter then "NO"
  else
    let len := intersectionEnd - intersectionStart
    if len ≥ 0 ∧ Nat.Prime len.natAbs then "YES"
    else "NO"

-- LLM HELPER
lemma bool_to_prop_hasIntersection (interval1: Int × Int) (interval2: Int × Int) :
  hasIntersection interval1 interval2 = true ↔ 
  let (s1, e1) := interval1
  let (s2, e2) := interval2
  max s1 s2 ≤ min e1 e2 := by
  simp [hasIntersection]

-- LLM HELPER
lemma implementation_yes_iff (interval1: Int × Int) (interval2: Int × Int) :
  let (s1, e1) := interval1
  let (s2, e2) := interval2
  s1 ≤ e1 → s2 ≤ e2 →
  (implementation interval1 interval2 = "YES" ↔ 
   max s1 s2 ≤ min e1 e2 ∧ Nat.Prime ((min e1 e2) - (max s1 s2)).natAbs) := by
  intro h1 h2
  simp [implementation]
  simp [h1, h2]
  by_cases h : max s1 s2 ≤ min e1 e2
  · simp [h]
    rfl
  · simp [h]
    constructor
    · intro h_eq
      exfalso
      simp at h_eq
    · intro ⟨h_contra, _⟩
      exact absurd h_contra h

-- LLM HELPER
lemma implementation_no_iff (interval1: Int × Int) (interval2: Int × Int) :
  let (s1, e1) := interval1
  let (s2, e2) := interval2
  s1 ≤ e1 → s2 ≤ e2 →
  (implementation interval1 interval2 = "NO" ↔ 
   ¬(max s1 s2 ≤ min e1 e2) ∨ ¬Nat.Prime ((min e1 e2) - (max s1 s2)).natAbs) := by
  intro h1 h2
  simp [implementation]
  simp [h1, h2]
  by_cases h : max s1 s2 ≤ min e1 e2
  · simp [h]
    by_cases hp : Nat.Prime ((min e1 e2) - (max s1 s2)).natAbs
    · simp [hp]
    · simp [hp]
  · simp [h]

-- LLM HELPER
lemma implementation_yes_or_no (interval1: Int × Int) (interval2: Int × Int) :
  implementation interval1 interval2 = "YES" ∨ implementation interval1 interval2 = "NO" := by
  simp [implementation]
  by_cases h1 : interval1.1 > interval1.2 ∨ interval2.1 > interval2.2
  · simp [h1]
  · simp [h1]
    by_cases h2 : max interval1.1 interval2.1 ≤ min interval1.2 interval2.2
    · simp [h2]
      by_cases h3 : 0 ≤ min interval1.2 interval2.2 - max interval1.1 interval2.1 ∧ 
                    Nat.Prime (min interval1.2 interval2.2 - max interval1.1 interval2.1).natAbs
      · simp [h3]
      · simp [h3]
    · simp [h2]

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  use implementation interval1 interval2
  constructor
  · rfl
  · intro h1 h2
    let (s1, e1) := interval1
    let (s2, e2) := interval2
    let intersectionStart := max s1 s2
    let intersectionEnd := min e1 e2
    let hasInter := intersectionStart ≤ intersectionEnd
    let isPrime := Nat.Prime (intersectionEnd - intersectionStart).natAbs
    constructor
    · constructor
      · intro h_yes
        constructor
        · rw [implementation_yes_iff] at h_yes
          exact h_yes.1
          exact h1
          exact h2
        · rw [implementation_yes_iff] at h_yes
          exact h_yes.2
          exact h1
          exact h2
      · intro ⟨h_hasInter, h_isPrime⟩
        rw [implementation_yes_iff]
        exact ⟨h_hasInter, h_isPrime⟩
        exact h1
        exact h2
    · constructor
      · constructor
        · intro h_no
          rw [implementation_no_iff] at h_no
          exact h_no
          exact h1
          exact h2
        · intro h_neg
          rw [implementation_no_iff]
          exact h_neg
          exact h1
          exact h2
      · exact implementation_yes_or_no interval1 interval2