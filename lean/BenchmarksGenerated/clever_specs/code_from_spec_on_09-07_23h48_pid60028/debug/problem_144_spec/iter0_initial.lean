def problem_spec
(implementation: String → String → Bool)
(x: String) (n: String) :=
let spec (result: Bool) :=
let fx := x.splitOn "/";
let fn := n.splitOn "/";
fx.length = 2 → fn.length = 2 →
fx.all String.isNat → fn.all String.isNat →
let p1 := fx[0]!.toNat!;
let q1 := fx[1]!.toNat!;
let p2 := fn[0]!.toNat!;
let q2 := fn[1]!.toNat!;
q1 ≠ 0 → q2 ≠ 0 →
(result ↔ (∃ k, k * p1 * p2 = q1 * q2))
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
def gcd (a b : Nat) : Nat :=
if b = 0 then a else gcd b (a % b)

-- LLM HELPER
def normalize_fraction (p q : Nat) : Nat × Nat :=
let d := gcd p q
(p / d, q / d)

def implementation (x: String) (n: String) : Bool := 
let fx := x.splitOn "/"
let fn := n.splitOn "/"
if fx.length = 2 && fn.length = 2 && fx.all String.isNat && fn.all String.isNat then
  let p1 := fx[0]!.toNat!
  let q1 := fx[1]!.toNat!
  let p2 := fn[0]!.toNat!
  let q2 := fn[1]!.toNat!
  if q1 ≠ 0 && q2 ≠ 0 then
    let (np1, nq1) := normalize_fraction p1 q1
    let (np2, nq2) := normalize_fraction p2 q2
    np1 * nq2 = nq1 * np2
  else
    false
else
  false

-- LLM HELPER
lemma gcd_dvd_left (a b : Nat) : gcd a b ∣ a := by
  sorry

-- LLM HELPER
lemma gcd_dvd_right (a b : Nat) : gcd a b ∣ b := by
  sorry

-- LLM HELPER
lemma gcd_pos (a b : Nat) (h : a > 0 ∨ b > 0) : gcd a b > 0 := by
  sorry

-- LLM HELPER
lemma normalize_fraction_correct (p q : Nat) (hq : q ≠ 0) : 
  let (np, nq) := normalize_fraction p q
  ∃ k, k * np = p ∧ k * nq = q ∧ k > 0 := by
  sorry

-- LLM HELPER
lemma fraction_eq_iff_cross_mult (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ 
  let (np1, nq1) := normalize_fraction p1 q1
  let (np2, nq2) := normalize_fraction p2 q2
  np1 * nq2 = nq1 * np2 := by
  sorry

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  unfold problem_spec
  unfold implementation
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  exists (if fx.length = 2 && fn.length = 2 && fx.all String.isNat && fn.all String.isNat then
    let p1 := fx[0]!.toNat!
    let q1 := fx[1]!.toNat!
    let p2 := fn[0]!.toNat!
    let q2 := fn[1]!.toNat!
    if q1 ≠ 0 && q2 ≠ 0 then
      let (np1, nq1) := normalize_fraction p1 q1
      let (np2, nq2) := normalize_fraction p2 q2
      np1 * nq2 = nq1 * np2
    else
      false
  else
    false)
  constructor
  · rfl
  · intro h1 h2 h3 h4 h5 h6
    simp [h1, h2, h3, h4, h5, h6]
    apply fraction_eq_iff_cross_mult
    · exact h5
    · exact h6