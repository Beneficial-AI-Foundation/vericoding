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
  String.mk (l.map fun b => if b then '1' else '0')

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
  dsimp [bits_to_string]
  -- Str2Int (String.mk xs) uses xs.data.foldl; here xs.data = l.map ...
  induction l with
  | nil => dsimp [String.mk]; simp [List.foldl]
  | cons b tl ih =>
    dsimp [String.mk]
    have : (b :: tl).map (fun b => if b then '1' else '0') = (if b then '1' else '0') :: tl.map (fun b => if b then '1' else '0') := rfl
    rw [this]
    dsimp [Str2Int]
    -- foldl over chars corresponds to foldl over bools using matching translator
    -- we proceed by case on b
    cases b
    · -- b = false
      simp [ih]
    · -- b = true
      simp [ih]

/-- Str2Int of NatToBinString equals the original natural number. -/
theorem Str2Int_NatToBinString (n : Nat) :
  Str2Int (NatToBinString n) = n := by
  dsimp [NatToBinString, bits_to_string, nat_bits]
  by_cases h0 : n = 0
  · -- n = 0
    simp [h0]
    rw [Str2Int_bits_to_string]
    simp [List.foldl]
    rfl
  · -- n ≠ 0
    have nb : nat_bits n = (nat_bits_rev n).reverse := by simp [nat_bits, h0]
    rw [nb, Str2Int_bits_to_string]
    -- prove by strong induction on n
    apply Nat.strongInductionOn n
    intro m IH
    cases m with
    | zero => contradiction
    | succ m' =>
      let mm := m' + 1
      let q := mm / 2
      let r := mm % 2
      -- definition of nat_bits_rev
      have nat_bits_rev_def : nat_bits_rev mm = ((mm % 2 = 1) :: nat_bits_rev q) := by
        dsimp [nat_bits_rev]; rfl
      have rev_eq : (nat_bits_rev mm).reverse = (nat_bits_rev q).reverse ++ [mm % 2 = 1] := by
        rw [nat_bits_rev_def, List.reverse_cons]; rfl
      rw [rev_eq, List.foldl_append]
      -- q < mm so we can use IH
      have qlt : q < mm := by
        have : 0 < 2 := by decide
        exact Nat.div_lt_self mm this
      have ihq := IH q qlt
      have ihq' : (nat_bits_rev q).reverse.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 = q := ihq
      rw [ihq']
      have : mm = 2 * q + r := by
        rw [Nat.div_mul_add_mod mm 2]
      dsimp
      cases r
      · -- r = 0
        simp [r] at this
        calc
          2 * q + 0 = 2 * q := rfl
          _ = mm := by rw [this]; simp
      · -- r = 1
        simp [r] at this
        calc
          2 * q + 1 = 2 * q + r := by simp
          _ = mm := by rw [this]; simp

/-- ValidBitString property holds for NatToBinString of any n. -/
theorem ValidBitString_NatToBinString (n : Nat) : ValidBitString (NatToBinString n) := by
  dsimp [NatToBinString, bits_to_string, nat_bits]
  intro i c hget
  by_cases h0 : n = 0
  · simp [h0] at hget
    dsimp [String.mk] at hget
    simp [List.get?_map] at hget
    rcases hget with ⟨b, hb⟩
    injection hb with hcc
    rw [←hcc]
    left; rfl
  · have nb : nat_bits n = (nat_bits_rev n).reverse := by simp [nat_bits, h0]
    rw [nb] at hget
    dsimp [bits_to_string, String.mk] at hget
    simp [List.get?_map] at hget
    rcases hget with ⟨b, hb⟩
    injection hb with hcc
    rw [←hcc]
    dsimp
    split_ifs with hb'
    · left; rfl
    · right; rfl

/-- Str2Int of a power-of-two string produced by make_pow_string equals Exp_int 2 n. -/
theorem Str2Int_make_pow_string (n : Nat) :
  Str2Int (make_pow_string n) = Exp_int 2 n := by
  dsimp [make_pow_string]
  -- use Str2Int_bits_to_string on (true :: replicate n false)
  have h := Str2Int_bits_to_string (true :: List.replicate n false)
  rw [h]
  -- show foldl yields 2^n
  induction n with
  | zero => simp [List.replicate, List.foldl, Exp_int]; rfl
  | succ n ih =>
    -- compute foldl on true :: replicate (n+1) false
    simp [List.replicate, List.foldl]
    -- foldl over the tail (replicate n false) with initial 1 yields 2 ^ n
    -- we show foldl (replicate n false) starting from 1 equals 2 ^ n
    have : (List.replicate n false).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 1 = 2 * (List.replicate n false).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 := by
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
-- </vc-proof>

end BignumLean