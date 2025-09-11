namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

-- <vc-helpers>
open List

-- LLM HELPER

/-- Convert a natural number to its little-endian list of bits (least significant bit first). -/
def nat_bits_rev : Nat → List Bool
  | 0     => []
  | n + 1 =>
    let b := (n + 1) % 2 = 1
    b :: nat_bits_rev ((n + 1) / 2)

/-- Convert a natural number to its big-endian list of bits (most significant bit first).
    We represent 0 as a single false bit (i.e., "0"). -/
def nat_bits (n : Nat) : List Bool :=
  if n = 0 then [false] else (nat_bits_rev n).reverse

/-- Convert a list of booleans (bits, MSB first) to a bitstring String. -/
def bits_to_string (l : List Bool) : String :=
  { data := l.map fun b => if b then '1' else '0' }

/-- Convert a natural number to its binary String representation (MSB-first).
    0 is represented as "0". -/
def NatToBinString (n : Nat) : String :=
  bits_to_string (nat_bits n)

/-- Helper producing a string representing 2^n, i.e., "1" followed by n zeros. -/
def make_pow_string (n : Nat) : String :=
  -- produce bits true :: replicate n false and convert via bits_to_string
  bits_to_string (true :: List.replicate n false)

/-- Str2Int on a bits_to_string equals folding the bits (with '1' as 1 and '0' as 0). -/
theorem Str2Int_bits_to_string (l : List Bool) :
  Str2Int (bits_to_string l) = l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 := by
  dsimp [bits_to_string, Str2Int]
  -- Str2Int { data := xs } = xs.foldl ...
  -- So we need to show map(...).foldl over chars equals foldl over bools
  induction l with
  | nil => simp
  | cons b tl ih =>
    simp [List.map, List.foldl]
    -- compute both sides; do case analysis on b
    cases b
    · simp [ih]
    · simp [ih]

/-- For our specific folding function f(acc,b) = 2*acc + val(b),
    folding over (reverse l) with foldl equals folding with foldr of the "rev" style function. -/
theorem foldl_reverse_eq_foldr (l : List Bool) :
  l.reverse.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 =
    l.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0 := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    dsimp [List.reverse]
    -- reverse (a::tl) = reverse tl ++ [a]
    have : (tl.reverse ++ [a]).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 =
           (tl.reverse.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0) |> fun t => 2 * t + (if a then 1 else 0) := by
      simp [List.foldl_append, List.foldl]; rfl
    rw [this]
    rw [ih]
    simp

/-- Define value of a little-endian bit list via foldr-style recursion. -/
def val_rev (l : List Bool) : Nat :=
  l.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0

/-- The little-endian bits produced by nat_bits_rev encode the number. -/
theorem val_rev_nat_bits_rev : ∀ n, val_rev (nat_bits_rev n) = n := by
  intro n
  induction n with
  | zero => simp [nat_bits_rev, val_rev]
  | succ n ih =>
    -- nat_bits_rev (n+1) = b :: nat_bits_rev ((n+1)/2) with b = (n+1)%2 = 1
    dsimp [nat_bits_rev, val_rev]
    let mm := n + 1
    let q := mm / 2
    let r := mm % 2
    have bdef : (mm % 2 = 1) = (r = 1) := rfl
    -- by definition val_rev (b :: rest) = (if b then 1 else 0) + 2 * val_rev rest
    have : (if (mm % 2 = 1) then 1 else 0) + 2 * val_rev (nat_bits_rev q) = mm := by
      -- use IH for q
      have q_lt : q < mm := by
        have two_pos : 0 < 2 := by decide
        exact Nat.div_lt_self mm two_pos
      have ihq := ih q_lt
      rw [←ihq]
      -- use div_mul_add_mod: mm = 2*q + r
      have dm := Nat.div_mul_add_mod mm 2
      dsimp [r] at dm
      -- simplify (if mm%2=1 then 1 else 0) is r
      have hr : (if mm % 2 = 1 then 1 else 0) = r := by
        cases r; simp
      rw [hr]
      -- now (r : Nat) + 2 * q = mm
      rw [Nat.add_comm, dm]; simp
    exact this

/-- Str2Int of NatToBinString equals the original natural number. -/
theorem Str2Int_NatToBinString (n : Nat) :
  Str2Int (NatToBinString n) = n := by
  dsimp [NatToBinString, nat_bits, bits_to_string]
  by_cases h0 : n = 0
  · -- n = 0
    simp [h0]
    -- bits_to_string [false] gives data = ['0']
    apply Str2Int_bits_to_string
  · -- n ≠ 0
    have nb : nat_bits n = (nat_bits_rev n).reverse := by
      simp [nat_bits, h0]
    -- rewrite and use Str2Int_bits_to_string
    rw [nb, Str2Int_bits_to_string]
    -- foldl over reverse equals val_rev, and val_rev(nat_bits_rev n) = n
    rw [←foldl_reverse_eq_foldr]
    -- foldr equals val_rev by definition
    dsimp [val_rev]
    apply val_rev_nat_bits_rev

/-- ValidBitString property holds for NatToBinString of any n. -/
theorem ValidBitString_NatToBinString (n : Nat) : ValidBitString (NatToBinString n) := by
  dsimp [NatToBinString, bits_to_string, nat_bits]
  intro i c hget
  by_cases h0 : n = 0
  · simp [h0] at hget
    dsimp [bits_to_string] at hget
    simp [List.get?_map] at hget
    rcases hget with ⟨b, hb⟩
    injection hb with hcc
    rw [←hcc]
    left; rfl
  · have nb : nat_bits n = (nat_bits_rev n).reverse := by simp [nat_bits, h0]
    rw [nb] at hget
    dsimp [bits_to_string] at hget
    simp [List.get?_map] at hget
    rcases hget with ⟨b, hb⟩
    injection hb with hcc
    rw [←hcc]
    dsimp
    cases b
    · right; rfl
    · left; rfl

/-- Str2Int of a power-of-two string produced by make_pow_string equals Exp_int 2 n. -/
theorem Str2Int_make_pow_string (n : Nat) :
  Str2Int (make_pow_string n) = Exp_int 2 n := by
  dsimp [make_pow_string]
  have h := Str2Int_bits_to_string (true :: List.replicate n false)
  rw [h]
  -- show foldl yields 2^n
  induction n with
  | zero => simp [List.replicate, List.foldl, Exp_int]; rfl
  | succ n ih =>
    simp [List.replicate, List.foldl]
    -- compute foldl: start with 1 then replicate n false
    -- show foldl (replicate n false) starting from 1 equals 2 * (foldl ... 0)
    have : (List.replicate n false).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 1 =
           2 * (List.replicate n false).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 := by
      induction n with
      | zero => simp
      | succ n ih' => simp [List.replicate] at ih'; simp [List.foldl, ih']
    rw [this, ih]
    simp [Exp_int]; rfl

/-- Exp_int obeys addition in exponent: Exp_int x (a + b) = Exp_int x a * Exp_int x b -/
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b with
  | zero => simp [Exp_int, Nat.add_zero]
  | succ b ih =>
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by
        dsimp [Exp_int]; split_ifs <;> simp_all
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (Exp_int x a) * (x * Exp_int x b) := by rw [mul_assoc]
      _ = (Exp_int x a) * Exp_int x (b + 1) := by
        dsimp [Exp_int]; split_ifs <;> simp_all

/-- Exp_int with 2^n exponent equals nested exponent: Exp_int x (Exp_int 2 n) = Exp_int (Exp_int x 2) n -/
theorem Exp_int_pow_two (x n : Nat) :
  Exp_int x (Exp_int 2 n) = Exp_int (Exp_int x 2) n := by
  induction n with
  | zero => simp [Exp_int]; rfl
  | succ n ih =>
    calc
      Exp_int x (Exp_int 2 (n + 1)) = Exp_int x (2 * Exp_int 2 n) := by dsimp [Exp_int]; split_ifs <;> simp_all
      _ = Exp_int x (Exp_int 2 n) * Exp_int x (Exp_int 2 n) := by
        have h := Exp_int_add x (Exp_int 2 n) (Exp_int 2 n)
        rw [h]
      _ = Exp_int (Exp_int x 2) (n + 1) := by
        rw [ih]; dsimp [Exp_int]; split_ifs <;> simp_all
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
/-- Modular exponentiation (general): return the canonical binary string of the numeric result. -/
def ModExp (sx sy sz : String) : String :=
  NatToBinString ((Exp_int (Str2Int sx) (Str2Int sy)) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
-- Unfold ModExp and use lemmas for NatToBinString
  dsimp [ModExp, NatToBinString]
  constructor
  · -- validity of produced string
    apply ValidBitString_NatToBinString
  · -- numeric equality: Str2Int (NatToBinString m) = m for any m
    apply Str2Int_NatToBinString
-- </vc-proof>

end BignumLean