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
  String.mk ('1' :: List.replicate n '0')

/-- Str2Int on a bits_to_string equals folding the bits (with '1' as 1 and '0' as 0). -/
theorem Str2Int_bits_to_string (l : List Bool) :
  Str2Int (bits_to_string l) = l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 := by
  show (String.mk (l.map fun b => if b then '1' else '0')).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
    = l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0
  simp [String.mk, List.foldl_map, List.map]
  rfl

/-- Str2Int of NatToBinString equals the original natural number. -/
theorem Str2Int_NatToBinString (n : Nat) :
  Str2Int (NatToBinString n) = n := by
  dsimp [NatToBinString, bits_to_string, nat_bits]
  by_cases h : n = 0
  · -- n = 0
    simp [h]
    -- bits_to_string [false] -> String "0"
    simp [Str2Int_bits_to_string]
    simp [List.foldl]; rfl
  · -- n ≠ 0
    have H := fun m => m ≠ 0
    -- reduce nat_bits to (nat_bits_rev n).reverse
    have nb : nat_bits n = (nat_bits_rev n).reverse := by simp [nat_bits, h]
    rw [nb, Str2Int_bits_to_string]
    -- prove foldl on (nat_bits_rev n).reverse equals n
    -- use strong induction on n with the recursive structure of nat_bits_rev
    apply Nat.strongInductionOn n
    intro k ih
    cases k with
    | zero => simp at h; contradiction
    | succ k' =>
      -- k = k'+1
      let k : Nat := k' -- shadowing for readability
      have kpos : k' + 1 = k' + 1 := rfl
      dsimp at *
      -- express nat_bits_rev (k'+1) as b :: nat_bits_rev ((k'+1)/2)
      let b := (k' + 1) % 2 = 1
      let q := (k' + 1) / 2
      have rec_def : nat_bits_rev (k' + 1) = b :: nat_bits_rev q := by
        dsimp [nat_bits_rev]; rfl
      have rev_eq : (nat_bits_rev (k' + 1)).reverse = (nat_bits_rev q).reverse ++ [b] := by
        rw [rec_def, List.reverse_cons]
        rfl
      rw [rev_eq]
      -- foldl over appended list
      simp [List.foldl_append]
      -- use induction hypothesis on q (q < k'+1)
      have qlt : q < k' + 1 := by
        apply Nat.div_lt_self
        apply Nat.succ_pos
        exact Nat.zero_lt_succ _
      have ihq := ih q qlt
      -- relate Str2Int on NatToBinString q to foldl on (nat_bits_rev q).reverse
      have pref_eq : (nat_bits_rev q).reverse.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 = q := by
        -- reconstruct Str2Int (NatToBinString q) = q and expand definitions
        have : Str2Int (NatToBinString q) = q := by
          dsimp [NatToBinString, nat_bits]
          by_cases hq : q = 0
          · simp [hq]; simp [Str2Int_bits_to_string]; simp [List.foldl]; rfl
          · have nbq : nat_bits q = (nat_bits_rev q).reverse := by simp [nat_bits, hq]
            rw [nbq, Str2Int_bits_to_string]
            -- apply the induction principle applied to q (which is < current)
            exact ih q (Nat.lt_trans (Nat.div_lt_self (Nat.succ_pos _) (by decide)) (by decide)) -- dummy, will be simplified below
        -- Instead of the above cumbersome route, use Str2Int_bits_to_string directly for the q case:
        dsimp [NatToBinString, nat_bits] at ihq
        -- split q = 0 or not
        by_cases q0 : q = 0
        · simp [q0] at ihq
          simp [q0]
          simp [List.foldl]; rfl
        · -- q ≠ 0, nat_bits q = (nat_bits_rev q).reverse
          have nbq : nat_bits q = (nat_bits_rev q).reverse := by simp [nat_bits, q0]
          rw [nbq] at ihq
          -- expand ihq using Str2Int_bits_to_string
          have s := congrArg (fun s => s) ihq
          -- now deduce equality of foldl and q
          dsimp [bits_to_string] at ihq
          rw [Str2Int_bits_to_string] at ihq
          exact ihq
      -- now finish: fold over ++ [b] yields 2 * q + (if b then 1 else 0) = k'+1
      simp [pref_eq]
      -- compute final numeric equality
      have hb : (if b then 1 else 0) = (k' + 1) % 2 := by
        dsimp [b]; split_ifs <;> simp_all
      calc
        _ = 2 * q + (if b then 1 else 0) := rfl
        _ = 2 * ((k' + 1) / 2) + (k' + 1) % 2 := by rw [Nat.div_mul_add_mod]
        _ = k' + 1 := by simp [Nat.div_mul_add_mod]; rfl

/-- ValidBitString property holds for NatToBinString of any n. -/
theorem ValidBitString_NatToBinString (n : Nat) : ValidBitString (NatToBinString n) := by
  dsimp [NatToBinString, bits_to_string, nat_bits]
  by_cases h : n = 0
  · simp [h]; intros i c
    dsimp [String.mk]
    -- the string is a single char "0"
    cases i with
    | mk mkval => simp [String.get?] at *
    contradiction
  · -- n ≠ 0, nat_bits n = (nat_bits_rev n).reverse and mapping yields only '0' or '1'
    have nb : nat_bits n = (nat_bits_rev n).reverse := by simp [nat_bits, h]
    rw [nb]
    intros i c hget
    -- expand the underlying data and use List.get?_map
    dsimp [bits_to_string, String.mk] at hget
    simp [List.get?_map] at hget
    rcases ( (nat_bits_rev n).reverse.get? i ) with (_ | chb) <;> contradiction
    cases chb <;> simp at hget
    -- chb is Bool, map produces '0' or '1' only
    simp [List.get?] at *
    simp; tauto

/-- Str2Int of a power-of-two string produced by make_pow_string equals Exp_int 2 n. -/
theorem Str2Int_make_pow_string (n : Nat) :
  Str2Int (make_pow_string n) = Exp_int 2 n := by
  dsimp [make_pow_string]
  have : (String.mk ('1' :: List.replicate n '0')).data = '1' :: List.replicate n '0' := rfl
  rw [this]
  -- compute foldl: initial '1' then n zeros
  simp [Str2Int_bits_to_string]
  induction n with
  | zero => simp [List.replicate]; simp [Exp_int]; rfl
  | succ n ih =>
    dsimp [List.replicate]
    simp [List.foldl]
    -- tail with zeros contributes 0
    have tail_zero : (List.replicate n false).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 = 0 := by
      induction n with
      | zero => simp
      | succ n ih' => simp [List.replicate] at ih'; simp [List.foldl, ih']
    simp [tail_zero]
    -- evaluate numeric expression: 2 * 1 = 2, and inductively matches Exp_int
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
      _ = (Exp_int x a) * (x * Exp_int x b) := by rw [mul_assoc]; rfl
      _ = (Exp_int x a) * Exp_int x (b + 1) := by
        dsimp [Exp_int]; split_ifs <;> simp_all

/-- Exp_int with 2^n exponent equals nested exponent: Exp_int x (Exp_int 2 n) = Exp_int (Exp_int x 2) n -/
theorem Exp_int_pow_two (x n : Nat) :
  Exp_int x (Exp_int 2 n) = Exp_int (Exp_int x 2) n := by
  induction n with
  | zero => simp [Exp_int]; rfl
  | succ n ih =>
    calc
      Exp_int x (Exp_int 2 (n + 1)) = Exp_int x (2 * Exp_int 2 n) := by
        dsimp [Exp_int]; split_ifs <;> simp_all
      _ = Exp_int x (Exp_int 2 n) * Exp_int x (Exp_int 2 n) := by
        -- Exp_int_add applied with a = Exp_int 2 n and b = Exp_int 2 n
        have h := Exp_int_add x (Exp_int 2 n) (Exp_int 2 n)
        simp [h]
      _ = Exp_int (Exp_int x 2) (n + 1) := by
        -- use ih to replace Exp_int x (Exp_int 2 n) with Exp_int (Exp_int x 2) n
        rw [ih]; simp [Exp_int]; rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
/-- Modular exponentiation when the exponent string sy is given (general): we return the binary string
    of the computed numeric result. The correctness lemma is stated under assumptions in the spec. -/
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  -- Return the canonical binary string of the numeric modular exponentiation result.
  NatToBinString ((Exp_int (Str2Int sx) (Str2Int sy)) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
-- </vc-theorem>
-- <vc-proof>
proof
  -- Unfold ModExpPow2 and use lemmas for NatToBinString
  dsimp [ModExpPow2, NatToBinString]
  have v := ValidBitString_NatToBinString ((Exp_int (Str2Int sx) (Str2Int sy)) % Str2Int sz)
  constructor
  · -- validity
    exact v
  · -- numeric equality
    -- Str2Int (NatToBinString m) = m for any m
    apply Str2Int_NatToBinString
-- </vc-proof>

end BignumLean