namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

-- <vc-helpers>
-- LLM HELPER
open Char

-- Helper: build a binary string of fixed bit-length (MSB first) for a given natural n.
def nat_bin_aux (n : Nat) : Nat → String
  | 0 =>
    -- bit for index 0 (LSB)
    String.push "" (if n % 2 = 1 then '1' else '0')
  | i+1 =>
    let ch := if (n / Exp_int 2 (i+1) % 2 = 1) then '1' else '0'
    -- produce MSB for position i+1, then append the representation for lower bits
    String.append (String.push "" ch) (nat_bin_aux n i)

-- Main converter with a bound on the highest index (must satisfy n < 2^(k+1)).
def Nat_to_bin_with_bound (n k : Nat) : String :=
  nat_bin_aux n k

-- LEMMAS FOR VERIFICATION

-- LLM HELPER
theorem Str2Int_push_singleton (c : Char) :
  Str2Int (String.push "" c) = (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- String.push "" c gives a data array with single element c
  -- Unfold to the underlying data fold and compute
  have : (String.push "" c).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
         (if c = '1' then 1 else 0) := by
    -- evaluate the fold over a single element
    simp [UArray.foldl] -- unfold UArray foldl for single element
    rfl
  exact this

-- LLM HELPER
theorem Str2Int_append (a b : String) :
  Str2Int (String.append a b) =
    Str2Int a * Exp_int 2 (b.length) + Str2Int b := by
  dsimp [Str2Int]
  -- Using the fact that the underlying data arrays concatenate and foldl over the concatenation
  -- equals folding over the second with the accumulator being the result of folding over the first.
  have : (a.data ++ b.data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
         b.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
                      (a.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
    -- UArray.foldl has the expected append property
    -- We use the general foldl append law; Lean's UArray provides foldlAppend behavior.
    apply UArray.foldl_append
  rw [this]
  -- Now show how feeding an initial accumulator corresponds to multiplication by a power of two
  -- We'll show by induction on b.length that doing the foldl with initial accumulator x equals x * 2^(b.length) + Str2Int b.
  have aux : ∀ x (b : UArray Char), (b.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) x) =
    x * Exp_int 2 (String.mkEmpty b.size |>.length) + (b.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
    -- We prove a more general fact by induction on the array size.
    intro x arr
    induction arr using UArray.inductionOn with
    | nil =>
      dsimp [UArray.foldl]
      simp
    | cons head tail ih =>
      dsimp [UArray.foldl]
      -- fold step: f (fold tail x) head
      have := ih ((if head = '1' then 1 else 0) + 2 * x)
      -- The above approach is fairly low-level; instead we can reason structurally:
      -- compute directly: foldl f x (head :: tail) = f (foldl f x tail) head = 2*(foldl f x tail) + digit head
      show (Array.mkCons head
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
open Char

-- Helper: build a binary string of fixed bit-length (MSB first) for a given natural n.
def nat_bin_aux (n : Nat) : Nat → String
  | 0 =>
    -- bit for index 0 (LSB)
    String.push "" (if n % 2 = 1 then '1' else '0')
  | i+1 =>
    let ch := if (n / Exp_int 2 (i+1) % 2 = 1) then '1' else '0'
    -- produce MSB for position i+1, then append the representation for lower bits
    String.append (String.push "" ch) (nat_bin_aux n i)

-- Main converter with a bound on the highest index (must satisfy n < 2^(k+1)).
def Nat_to_bin_with_bound (n k : Nat) : String :=
  nat_bin_aux n k

-- LEMMAS FOR VERIFICATION

-- LLM HELPER
theorem Str2Int_push_singleton (c : Char) :
  Str2Int (String.push "" c) = (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- String.push "" c gives a data array with single element c
  -- Unfold to the underlying data fold and compute
  have : (String.push "" c).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
         (if c = '1' then 1 else 0) := by
    -- evaluate the fold over a single element
    simp [UArray.foldl] -- unfold UArray foldl for single element
    rfl
  exact this

-- LLM HELPER
theorem Str2Int_append (a b : String) :
  Str2Int (String.append a b) =
    Str2Int a * Exp_int 2 (b.length) + Str2Int b := by
  dsimp [Str2Int]
  -- Using the fact that the underlying data arrays concatenate and foldl over the concatenation
  -- equals folding over the second with the accumulator being the result of folding over the first.
  have : (a.data ++ b.data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
         b.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
                      (a.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
    -- UArray.foldl has the expected append property
    -- We use the general foldl append law; Lean's UArray provides foldlAppend behavior.
    apply UArray.foldl_append
  rw [this]
  -- Now show how feeding an initial accumulator corresponds to multiplication by a power of two
  -- We'll show by induction on b.length that doing the foldl with initial accumulator x equals x * 2^(b.length) + Str2Int b.
  have aux : ∀ x (b : UArray Char), (b.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) x) =
    x * Exp_int 2 (String.mkEmpty b.size |>.length) + (b.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
    -- We prove a more general fact by induction on the array size.
    intro x arr
    induction arr using UArray.inductionOn with
    | nil =>
      dsimp [UArray.foldl]
      simp
    | cons head tail ih =>
      dsimp [UArray.foldl]
      -- fold step: f (fold tail x) head
      have := ih ((if head = '1' then 1 else 0) + 2 * x)
      -- The above approach is fairly low-level; instead we can reason structurally:
      -- compute directly: foldl f x (head :: tail) = f (foldl f x tail) head = 2*(foldl f x tail) + digit head
      show (Array.mkCons head
-- </vc-code>

end BignumLean