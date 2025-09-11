namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
theorem foldl_bin (l : List Char) (acc : Nat) :
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc =
    acc * 2 ^ l.length + l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction l generalizing acc with
  | nil => simp [List.foldl, Nat.pow, Nat.mul_one, Nat.zero_add]
  | cons hd tl ih =>
    simp [List.foldl]
    -- apply IH to the accumulator 2*acc + bit and to the accumulator corresponding to hd
    let bit := (if hd = '1' then 1 else 0)
    have H1 := ih (2 * acc + bit)
    have H2 := ih bit
    -- H1: foldl f tl (2*acc + bit) = (2*acc + bit) * 2^tl.length + foldl f 0 tl
    -- H2: foldl f tl bit = bit * 2^tl.length + foldl f 0 tl
    -- We need to show foldl f tl (2*acc + bit) = acc * 2^(tl.length+1) + foldl f tl bit
    -- Rearrangement and algebra finishes the proof
    dsimp [bit] at H1 H2
    calc
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * acc + bit) tl
        = (2 * acc + bit) * 2 ^ tl.length + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tl := by
          exact H1
      _ = acc * 2 ^ (tl.length + 1) + (bit * 2 ^ tl.length + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tl) := by
          simp [Nat.pow_succ, Nat.mul_assoc]; ring
      _ = acc * 2 ^ (tl.length + 1) + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) bit tl := by
          -- use H2 rewritten: bit * 2^tl.length + foldl ... 0 tl = foldl ... tl bit
          rw [←H2]; rfl

-- LLM HELPER
theorem Str2Int_append (s1 s2 : String) :
  Str2Int (s1 ++ s2) = (Str2Int s1) * 2 ^ (s2.length) + Str2Int s2 := by
  have : (s1 ++ s2).data = s1.data ++ s2.data := rfl
  dsimp [Str2Int]
  rw [this]
  -- apply foldl_bin to the second list with acc = Str2Int s1
  let acc := s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
  have h := foldl_bin s2.data acc
  -- h states: (s2.data).foldl f acc = acc * 2 ^ s2.data.length + s2.data.foldl f 0
  -- but acc is exactly Str2Int s1 and data lengths coincide with String.length
  simp [acc] at h
  exact h

-- LLM HELPER
def nat_to_bit_string : Nat → String
  | 0 => "0"
  | n+1 =>
    let k := n + 1
    let m := k / 2
    let rest := nat_to_bit_string m
    let bit := if k % 2 = 1 then '1' else '0'
    rest ++ String.mk bit ""
  termination_by nat_to_bit_string n => n
  decreasing_by
    intro
    have : (n + 1) / 2 < n + 1 := by
      apply Nat.div_lt_self
      decide
    exact this

-- LLM HELPER
theorem nat_to_bit_string_correct : ∀ n, Str2Int (nat_to_bit_string n) = n := by
  intro n
  induction n with
  | zero => dsimp [nat_to_bit_string, Str2Int]; simp
  | succ n ih =>
    let k := n + 1
    dsimp [nat_to_bit_string]
    let m := k / 2
    let rest := nat_to_bit_string m
    let bit := if k % 2 = 1 then '1' else '0'
    have ihm : Str2Int rest = m := by
      apply ih
    -- use append lemma with s2 = single-character string
    have happend := Str2Int_append rest (String.mk bit "")
    -- compute Str2Int of single-character string
    have hbit : Str2Int (String.mk bit "") = (if bit = '1' then 1 else 0) := by
      dsimp [Str2Int]
      -- underlying data is [bit]
      simp
    -- combine
    have H : Str2Int (rest ++ String.mk bit "") =
             m * 2 ^ (String.mk bit "".length) + (if bit = '1' then 1 else 0) := by
      rw [happend, ihm, hbit]
    -- String.mk bit "" has length 1, so 2^1 = 2
    have H2 : Str2Int (rest ++ String.mk bit "") = 2 * m + (if bit = '1' then 1 else 0) := by
      rw [H]; simp
    -- show (if bit = '1' then 1 else 0) = k % 2
    have bit_eq_mod : (if bit = '1' then 1 else 0) = k % 2 := by
      dsimp [bit]
      let r := k % 2
      have r_lt : r < 2 := Nat.mod_lt k (by decide)
      cases r with
      | zero => simp [r]
      | succ r' =>
        have : r' = 0 := by
          have : succ r' < 2 := r_lt
          linarith
        simp [this]
    -- finish by rewriting and using div_mod identity
    calc
      Str2Int (rest ++ String.mk bit "") = 2 * m + (if bit = '1' then 1 else 0) := by exact H2
      _ = 2 * m + k % 2 := by rw [bit_eq_mod]
      _ = k := by
        -- k = 2*(k/2) + k%2
        rw [Nat.div_mod_eq]
        rfl
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def Mul (s1 s2 : String) : String :=
  nat_to_bit_string (Str2Int s1 * Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) : Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 :=
-- </vc-theorem>
-- <vc-proof>
by
  dsimp [Mul]
  let n := Str2Int s1 * Str2Int s2
  show Str2Int (nat_to_bit_string n) = n
  apply nat_to_bit_string_correct
-- </vc-proof>

end BignumLean