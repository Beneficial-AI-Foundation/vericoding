-- <vc-preamble>
def dec (n : Nat) : List PrimeFactor := sorry

def decomp (n : Nat) : String := sorry

def splitString (s : String) (sep : String) : List String := sorry
def contains (s : String) (sub : String) : Bool := sorry

def toNat! (s : String) : Nat := sorry
def sorted (l : List Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distinct (l : List Nat) : Bool := sorry

theorem dec_reconstruction {n : Nat} (h : n ≥ 2) :
  let factors := dec n
  let reconstructed := factors.foldl (fun acc f => acc * f.prime^f.power) 1
  reconstructed = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dec_primes {n : Nat} (h : n ≥ 2) :
  let factors := dec n
  ∀ f ∈ factors, 
    ∀ i : Nat, 2 ≤ i → i * i ≤ f.prime → f.prime % i ≠ 0 := sorry

theorem decomp_format {n : Nat} (h : n ≥ 2) :
  let result := decomp n
  let factors := splitString result " * "
  ∀ f ∈ factors, 
    (contains f "^" → 
      let parts := splitString f "^"
      (parts.length = 2) ∧ 
      let base := parts.head!
      let power := parts.get! 1
      toNat! base > 0 ∧ toNat! power > 0) ∧
    (¬contains f "^" → toNat! f > 0) := sorry

theorem decomp_ascending {n : Nat} (h : n ≥ 2) :
  let result := decomp n
  let factors := splitString result " * "
  let bases := factors.map (fun f => 
    if contains f "^" 
    then toNat! (splitString f "^").head!
    else toNat! f)
  sorted bases := sorry

theorem decomp_unique {n : Nat} (h : n ≥ 2) :
  let result := decomp n
  let factors := splitString result " * "
  let bases := factors.map (fun f => 
    if contains f "^" 
    then toNat! (splitString f "^").head!
    else toNat! f)
  distinct bases := sorry
-- </vc-theorems>