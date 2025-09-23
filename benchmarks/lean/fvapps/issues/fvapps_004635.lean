-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Random.new (s : Int) : Random := sorry

theorem seed_initialization (s : Int) :
  (Random.new s).seed = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem random_bounds (r : Random) :
  0 ≤ r.random ∧ r.random ≤ 1 := sorry

theorem randint_bounds (s start finish : Int) :
  let r := Random.new s
  let lo := min start finish
  let hi := max start finish
  lo ≤ r.randint lo hi ∧ r.randint lo hi ≤ hi := sorry

theorem randint_deterministic (s start : Int) :
  let r1 := Random.new s
  let r2 := Random.new s
  let finish := start + Int.natAbs (s % 1000)
  r1.randint start finish = r2.randint start finish := sorry

theorem random_advances_seed (s : Int) :
  let r := Random.new s
  let initial_seed := r.seed
  r.seed + 1 = initial_seed + 1 := sorry
-- </vc-theorems>