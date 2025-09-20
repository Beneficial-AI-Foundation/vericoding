-- <vc-preamble>
def noDups {α} [BEq α] (as : List α) : List α :=
  as.foldl (fun acc a => if acc.contains a then acc else a::acc) []

def countUnique (s : String) : Nat :=
  (noDups s.data).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorial (n : Nat) : Nat := sorry

def permutations (s : String) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem permutation_length_factorial_bound
  (s : String) (hs : s.length > 0) :
  let perms := permutations s
  let n_unique := countUnique s
  (n_unique = s.length → perms.length = factorial s.length) ∧
  (n_unique < s.length → perms.length ≤ factorial s.length) :=
sorry

theorem permutations_same_length
  (s : String) (hs : s.length > 0) :
  let perms := permutations s
  ∀ p ∈ perms, p.length = s.length :=
sorry

theorem permutations_use_original_chars
  (s : String) (hs : s.length > 0) :
  let perms := permutations s
  ∀ p ∈ perms, p.data.toArray.qsort (· ≤ ·) = s.data.toArray.qsort (· ≤ ·) :=
sorry

theorem permutations_are_unique
  (s : String) (hs : s.length > 0) :
  let perms := permutations s
  perms.length = (noDups perms).length :=
sorry
-- </vc-theorems>