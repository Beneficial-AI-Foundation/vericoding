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
-- LLM HELPER
open List

/-- Convert a natural number to its little-endian list of bits (least significant bit first). -/
def nat_bits_rev : Nat → List Bool
  | 0 => []
  | n+1 =>
    let b := (n+1) % 2 = 1
    b :: nat_bits_rev ((n+1) / 2)

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

-- Lemmas about the conversion routines

-- LLM HELPER
theorem Str2Int_bits_to_string (l : List Bool) :
  Str2Int (bits_to_string l) = l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 := by
  -- Str2Int uses the underlying .data which for String.mk is exactly the list supplied.
  show (String.mk (l.map fun b => if b then '1' else '0')).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
    = l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0
  simp [String.mk, List.foldl_map, List.map]; rfl

-- LLM HELPER
theorem Str2Int_NatToBinString (n : Nat) :
  Str2Int (NatToBinString n) = n := by
  dsimp [NatToBinString, nat_bits, bits_to_string]
  split
  · -- case n = 0
    intro hn
    simp [hn, Str2Int_bits_to_string]
    simp [List.foldl, Nat.zero_eq, Nat.zero_add]; rfl
  · -- case n ≠ 0
    intro hn
    have : nat_bits n = (nat_bits_rev n).reverse := by simp [nat_bits, hn]
    dsimp [bits_to_string]
    rw [this, Str2Int_bits_to_string]
    -- Now show that folding the reversed rev bits yields n.
    -- We prove by induction on n using the structure of nat_bits_rev.
    induction n using Nat.strongInductionOn with
    | ih n =>
      cases n
      · contradiction
      have hnpos : n+1 > 0 := by decide
      -- Let b = (n+1) % 2 = 1, k = (n+1) / 2
      let b := (n+1) % 2 = 1
      let k := (n+1) / 2
      have rec_def : nat_bits_rev (n+1) = b :: nat_bits_rev k := by
        dsimp [nat_bits_rev]; rfl
      have rev_eq : (nat_bits_rev (n+1)).reverse = (nat_bits_rev k).reverse ++ [b] := by
        rw [rec_def, List.reverse_cons]; rfl
      rw [rev_eq]
      simp [List.foldl_append, Str2Int_bits_to_string]
      -- Now use the induction hypothesis on k
      have hk_lt : k < n+1 := by
        apply Nat.div_lt_self (Nat.lt_of_lt_succ (Nat.succ_pos n))
        decide
      have ihk := ih k hk_lt
      -- compute fold for prefix
      have pref :
        (nat_bits_rev k).reverse.foldl (fun acc b' => 2 * acc + (if b' then 1 else 0)) 0 = k := by
        -- use ihk rewritten to the required form
        have := by
          dsimp [NatToBinString, nat_bits] at ihk
          -- ihk states Str2Int (NatToBinString k) = k; expand definitions to extract the foldl equality
          dsimp [NatToBinString] at ihk
          cases (k = 0) <;> contradiction
        -- Instead of the above roundabout, use ihk by re-evaluating Str2Int_bits_to_string for k
        have : Str2Int (bits_to_string ((nat_bits_rev k).reverse)) = k := by
          -- bits_to_string of reverse equals NatToBinString k when k ≠ 0
          dsimp [NatToBinString, nat_bits] at ihk
          assumption
        simpa using this
      -- Now finish
      simp [pref]
      -- fold over appended [b] gives 2 * k + (if b then 1 else 0) = n+1
      have hb : (if b then 1 else 0) = (n+1) % 2 := by
        dsimp [b]; split_ifs <;> simp_all
      calc
        _ = 2 * k + (if b then 1 else 0) := rfl
        _ = 2 * ((n+1) / 2) + (n+1) % 2 := by rw [Nat.div_mul_add_mod]
        _ = n+1 := by
          rw [Nat.div_mul_add_mod, Nat.add_comm]; rfl

-- LLM HELPER
theorem ValidBitString_NatToBinString (n : Nat) : ValidBitString (NatToBinString n) := by
  dsimp [NatToBinString, bits_to_string]
  by_cases h : n = 0
  · simp [h]; intros i c; simp [String.mk]; -- single char "0"
    cases i <;> simp at *; contradiction <|> simp_all
  · -- For n ≠ 0, nat_bits n = (nat_bits_rev n).reverse, and bits_to_string maps booleans to '0'/'1'
    dsimp [nat_bits] at h
    simp [h]
    intros i c
    have : (String.mk ((nat_bits_rev n).reverse.map fun b => if b then '1' else '0')).data = (nat_bits_rev n).reverse.map fun b => if b then '1' else '0' := rfl
    simp [this] at *
    -- now inspect the character at position i
    intro hi
    -- the map yields only '0' or '1'
    cases ( (nat_bits_rev n).reverse.map fun b => if b then '1' else '0' ).get? i with
    | none => contradiction
    | some ch =>
      simp [List.get?_map] at hi
      injection hi with hch
      subst hch
      simp; tauto

-- LLM HELPER
theorem Str2Int_make_pow_string (n : Nat) :
  Str2Int (make_pow_string n) = Exp_int 2 n := by
  dsimp [make_pow_string]
  -- make_pow_string n = String.mk ('1' :: replicate n '0')
  have : (String.mk ('1' :: List.replicate n '0')).data = '1' :: List.replicate n '0' := rfl
  simp [this, Str2Int_bits_to_string]
  -- The list of bits is [true, false, ..., false], fold gives 2^n
  induction n with
  | zero =>
    simp [List.replicate, List.foldl]; -- single '1'
    simp [Exp_int]; rfl
  | succ n ih =>
    -- replicate (n+1) '0' = '0' :: replicate n '0'
    dsimp [List.replicate]
    -- compute fold on (true :: false :: ... :: false)
    simp [List.foldl]
    -- fold on tail yields 2^n
    have tail : (List.replicate n false).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 = 0 := by
      induction n with
      | zero => simp
      | succ n ihn =>
        simp [List.replicate] at ihn
        simp [List.foldl, ihn]
    simp [tail]
    -- so overall: 2 * 1 + 0 = 2 and then repeated succ gives 2^(n+1)
    -- use Exp_int definition
    simp [Exp_int]; rfl

-- LLM HELPER
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b with
  | zero => simp [Exp_int, Nat.add_zero]
  | succ b ih =>
    simp [Nat.add_comm, Nat.add_succ, Nat.add_assoc]
    show Exp_int x (a + b + 1) = Exp_int x (a + b) * x
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by
        dsimp [Exp_int]; split_ifs <;> simp_all
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (Exp_int x a) * (x * Exp_int x b) := by rw [mul_assoc]; rfl
      _ = (Exp_int x a) * Exp_int x (b + 1) := by
        dsimp [Exp_int]; split_ifs <;> simp_all

-- LLM HELPER
theorem Exp_int_pow_two (x n : Nat) :
  Exp_int x (Exp_int 2 n) = Exp_int (Exp_int x 2) n := by
  induction n with
  | zero => simp [Exp_int]; rfl
  | succ n ih =>
    calc
      Exp_int x (Exp_int 2 (n + 1)) = Exp_int x (2 * Exp_int 2 n) := by
        dsimp [Exp_int]; split_ifs <;> simp_all
      _ = Exp_int x (Exp_int 2 n) * Exp_int x (Exp_int 2 n) := by
        -- use Exp_int_add repeatedly: Exp x (u+u) = Exp x u * Exp x u
        have h := Exp_int_add x (Exp_int 2
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
open List

/-- Convert a natural number to its little-endian list of bits (least significant bit first). -/
def nat_bits_rev : Nat → List Bool
  | 0 => []
  | n+1 =>
    let b := (n+1) % 2 = 1
    b :: nat_bits_rev ((n+1) / 2)

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

-- Lemmas about the conversion routines

-- LLM HELPER
theorem Str2Int_bits_to_string (l : List Bool) :
  Str2Int (bits_to_string l) = l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 := by
  -- Str2Int uses the underlying .data which for String.mk is exactly the list supplied.
  show (String.mk (l.map fun b => if b then '1' else '0')).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
    = l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0
  simp [String.mk, List.foldl_map, List.map]; rfl

-- LLM HELPER
theorem Str2Int_NatToBinString (n : Nat) :
  Str2Int (NatToBinString n) = n := by
  dsimp [NatToBinString, nat_bits, bits_to_string]
  split
  · -- case n = 0
    intro hn
    simp [hn, Str2Int_bits_to_string]
    simp [List.foldl, Nat.zero_eq, Nat.zero_add]; rfl
  · -- case n ≠ 0
    intro hn
    have : nat_bits n = (nat_bits_rev n).reverse := by simp [nat_bits, hn]
    dsimp [bits_to_string]
    rw [this, Str2Int_bits_to_string]
    -- Now show that folding the reversed rev bits yields n.
    -- We prove by induction on n using the structure of nat_bits_rev.
    induction n using Nat.strongInductionOn with
    | ih n =>
      cases n
      · contradiction
      have hnpos : n+1 > 0 := by decide
      -- Let b = (n+1) % 2 = 1, k = (n+1) / 2
      let b := (n+1) % 2 = 1
      let k := (n+1) / 2
      have rec_def : nat_bits_rev (n+1) = b :: nat_bits_rev k := by
        dsimp [nat_bits_rev]; rfl
      have rev_eq : (nat_bits_rev (n+1)).reverse = (nat_bits_rev k).reverse ++ [b] := by
        rw [rec_def, List.reverse_cons]; rfl
      rw [rev_eq]
      simp [List.foldl_append, Str2Int_bits_to_string]
      -- Now use the induction hypothesis on k
      have hk_lt : k < n+1 := by
        apply Nat.div_lt_self (Nat.lt_of_lt_succ (Nat.succ_pos n))
        decide
      have ihk := ih k hk_lt
      -- compute fold for prefix
      have pref :
        (nat_bits_rev k).reverse.foldl (fun acc b' => 2 * acc + (if b' then 1 else 0)) 0 = k := by
        -- use ihk rewritten to the required form
        have := by
          dsimp [NatToBinString, nat_bits] at ihk
          -- ihk states Str2Int (NatToBinString k) = k; expand definitions to extract the foldl equality
          dsimp [NatToBinString] at ihk
          cases (k = 0) <;> contradiction
        -- Instead of the above roundabout, use ihk by re-evaluating Str2Int_bits_to_string for k
        have : Str2Int (bits_to_string ((nat_bits_rev k).reverse)) = k := by
          -- bits_to_string of reverse equals NatToBinString k when k ≠ 0
          dsimp [NatToBinString, nat_bits] at ihk
          assumption
        simpa using this
      -- Now finish
      simp [pref]
      -- fold over appended [b] gives 2 * k + (if b then 1 else 0) = n+1
      have hb : (if b then 1 else 0) = (n+1) % 2 := by
        dsimp [b]; split_ifs <;> simp_all
      calc
        _ = 2 * k + (if b then 1 else 0) := rfl
        _ = 2 * ((n+1) / 2) + (n+1) % 2 := by rw [Nat.div_mul_add_mod]
        _ = n+1 := by
          rw [Nat.div_mul_add_mod, Nat.add_comm]; rfl

-- LLM HELPER
theorem ValidBitString_NatToBinString (n : Nat) : ValidBitString (NatToBinString n) := by
  dsimp [NatToBinString, bits_to_string]
  by_cases h : n = 0
  · simp [h]; intros i c; simp [String.mk]; -- single char "0"
    cases i <;> simp at *; contradiction <|> simp_all
  · -- For n ≠ 0, nat_bits n = (nat_bits_rev n).reverse, and bits_to_string maps booleans to '0'/'1'
    dsimp [nat_bits] at h
    simp [h]
    intros i c
    have : (String.mk ((nat_bits_rev n).reverse.map fun b => if b then '1' else '0')).data = (nat_bits_rev n).reverse.map fun b => if b then '1' else '0' := rfl
    simp [this] at *
    -- now inspect the character at position i
    intro hi
    -- the map yields only '0' or '1'
    cases ( (nat_bits_rev n).reverse.map fun b => if b then '1' else '0' ).get? i with
    | none => contradiction
    | some ch =>
      simp [List.get?_map] at hi
      injection hi with hch
      subst hch
      simp; tauto

-- LLM HELPER
theorem Str2Int_make_pow_string (n : Nat) :
  Str2Int (make_pow_string n) = Exp_int 2 n := by
  dsimp [make_pow_string]
  -- make_pow_string n = String.mk ('1' :: replicate n '0')
  have : (String.mk ('1' :: List.replicate n '0')).data = '1' :: List.replicate n '0' := rfl
  simp [this, Str2Int_bits_to_string]
  -- The list of bits is [true, false, ..., false], fold gives 2^n
  induction n with
  | zero =>
    simp [List.replicate, List.foldl]; -- single '1'
    simp [Exp_int]; rfl
  | succ n ih =>
    -- replicate (n+1) '0' = '0' :: replicate n '0'
    dsimp [List.replicate]
    -- compute fold on (true :: false :: ... :: false)
    simp [List.foldl]
    -- fold on tail yields 2^n
    have tail : (List.replicate n false).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 = 0 := by
      induction n with
      | zero => simp
      | succ n ihn =>
        simp [List.replicate] at ihn
        simp [List.foldl, ihn]
    simp [tail]
    -- so overall: 2 * 1 + 0 = 2 and then repeated succ gives 2^(n+1)
    -- use Exp_int definition
    simp [Exp_int]; rfl

-- LLM HELPER
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b with
  | zero => simp [Exp_int, Nat.add_zero]
  | succ b ih =>
    simp [Nat.add_comm, Nat.add_succ, Nat.add_assoc]
    show Exp_int x (a + b + 1) = Exp_int x (a + b) * x
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by
        dsimp [Exp_int]; split_ifs <;> simp_all
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (Exp_int x a) * (x * Exp_int x b) := by rw [mul_assoc]; rfl
      _ = (Exp_int x a) * Exp_int x (b + 1) := by
        dsimp [Exp_int]; split_ifs <;> simp_all

-- LLM HELPER
theorem Exp_int_pow_two (x n : Nat) :
  Exp_int x (Exp_int 2 n) = Exp_int (Exp_int x 2) n := by
  induction n with
  | zero => simp [Exp_int]; rfl
  | succ n ih =>
    calc
      Exp_int x (Exp_int 2 (n + 1)) = Exp_int x (2 * Exp_int 2 n) := by
        dsimp [Exp_int]; split_ifs <;> simp_all
      _ = Exp_int x (Exp_int 2 n) * Exp_int x (Exp_int 2 n) := by
        -- use Exp_int_add repeatedly: Exp x (u+u) = Exp x u * Exp x u
        have h := Exp_int_add x (Exp_int 2
-- </vc-code>

end BignumLean