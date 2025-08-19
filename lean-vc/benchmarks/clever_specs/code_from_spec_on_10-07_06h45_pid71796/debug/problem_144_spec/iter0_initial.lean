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
def simplify_fraction (p q : Nat) : Nat × Nat :=
if q = 0 then (0, 1)
else
  let g := gcd p q
  (p / g, q / g)

def implementation (x: String) (n: String) : Bool :=
let fx := x.splitOn "/"
let fn := n.splitOn "/"
if fx.length = 2 && fn.length = 2 &&
   fx.all String.isNat && fn.all String.isNat then
  let p1 := fx[0]!.toNat!
  let q1 := fx[1]!.toNat!
  let p2 := fn[0]!.toNat!
  let q2 := fn[1]!.toNat!
  if q1 ≠ 0 && q2 ≠ 0 then
    let (p1_simp, q1_simp) := simplify_fraction p1 q1
    let (p2_simp, q2_simp) := simplify_fraction p2 q2
    p1_simp * q2_simp = q1_simp * p2_simp
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
lemma simplify_fraction_correct (p q : Nat) (hq : q ≠ 0) :
  let (p', q') := simplify_fraction p q
  ∃ k, k * p' = p ∧ k * q' = q ∧ q' ≠ 0 := by
  sorry

-- LLM HELPER
lemma cross_mult_iff_prop_equal (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ 
  (let (p1', q1') := simplify_fraction p1 q1
   let (p2', q2') := simplify_fraction p2 q2
   p1' * q2' = q1' * p2') := by
  sorry

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  unfold problem_spec
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  use implementation x n
  constructor
  · rfl
  · intro h1 h2 h3 h4
    let p1 := fx[0]!.toNat!
    let q1 := fx[1]!.toNat!
    let p2 := fn[0]!.toNat!
    let q2 := fn[1]!.toNat!
    intro hq1 hq2
    unfold implementation
    simp [h1, h2, h3, h4, hq1, hq2]
    exact cross_mult_iff_prop_equal p1 q1 p2 q2 hq1 hq2