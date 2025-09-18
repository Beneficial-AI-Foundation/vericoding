-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_number_of_frogs (s: String) : Int := sorry

def is_valid_croak (s: String) : Bool :=
  let counts := ['c', 'r', 'o', 'a', 'k'].map (fun c => s.data.count c)
  counts.all (· = counts[0]!) ∧ 
  s.length % 5 = 0 ∧ 
  (s.length > 0 → s.data[0]! = 'c') ∧
  (s.length > 0 → s.data[s.length - 1]! = 'k')
-- </vc-definitions>

-- <vc-theorems>
theorem min_frogs_upper_bound (n_frogs n_times: Nat) (s: String) :
  s = String.join (List.replicate (n_frogs * n_times) "croak") →
  min_number_of_frogs s ≤ n_frogs
  := sorry
-- </vc-theorems>