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
  | nil =>
    -- []: foldl f acc = acc and foldl f 0 [] = 0, 2^0 = 1
    simp [List.foldl]
    simp [Nat.pow_zero]
  | cons hd tl ih =>
    let f := fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)
    simp [List.foldl]
    let bit := (if hd = '1' then 1 else 0)
    have H := ih (2 * acc + bit)
    have H0 := ih bit
    -- Use H to expand the left hand side, then rearrange algebraically and apply H0
    rw [H]
    -- (2*acc + bit) * 2^tl.length + foldl f 0 tl
    -- distribute the multiplication
    rw [Nat.mul_add]
    -- (2*acc) * 2^tl.length + bit * 2^tl.length + foldl f 0 tl
    -- associate to get 2 * (acc * 2^tl.length)
    rw [←Nat.mul_assoc]
    -- 2 * (acc * 2^tl.length) + bit * 2^tl.length + foldl f 0 tl
    -- commute the 2 with the acc*2^tl.length factor to prepare pow_succ
    rw [Nat.mul_comm 2 (acc * 2 ^ tl.length)]
    rw [Nat.mul_assoc]
    -- now use pow_succ: 2 * 2^tl.length = 2^(tl.length+1)
    rw [←Nat.mul_assoc]
    rw [Nat.pow_succ]
    -- replace bit * 2^tl.length + foldl f 0 tl with foldl f tl bit using H0
    rw [←H0]
    -- foldl f tl bit = foldl f 0 (hd :: tl)
    rfl

-- LLM HELPER
theorem Str2Int_append (s1 s2 : String) :
  Str2Int (s1 ++ s2) = (Str2Int s1) * 2 ^ (s2.length) + Str2Int s2 := by
  dsimp [Str2Int]
  -- underlying data of concatenation
  have hdata : (s1 ++ s2).data = s1.data ++ s2.data := rfl
  rw [hdata]
  let f := fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)
  -- foldl on appended lists
  have happend := List.foldl_append f 0 s1.data s2.data
  -- happend : (s1.data ++ s2.data).foldl f 0 = s2.data.foldl f (s1.data.foldl f 0)
  rw [happend]
  -- apply foldl_bin to s2.data with acc = Str2Int s1
  have H := foldl_bin s2.data (s1.data.foldl f 0)
  dsimp [Str2Int] at H
  -- H : s2.data.foldl f (Str2Int s1) = Str2Int s1 * 2 ^ s2.data.length + s2.data.foldl f 0
  rw [H]

-- LLM HELPER
def nat_to_bit_string : Nat → String
  | 0 => "0"
  | n+1 =>
    let k := n + 1
    let m := k / 2
    let rest := nat_to_bit_string m
    let bit := if k % 2 = 1 then '1' else '0'
    rest ++ String.mk bit ""
  termination_by n => n
  decreasing_by
    intro n
    -- show (n+1)/2 < n+1
    apply Nat.div_lt_self
    decide

-- LLM HELPER
theorem nat_to_bit_string_correct : ∀ n, Str2Int (nat_to_bit_string n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n with
    | zero =>
      -- nat_to_bit_string 0 = "0"
      simp [nat_to_bit_string, Str2Int]
    | succ n' =>
      let k := n' + 1
      let m := k / 2
      -- m < k, so use strong induction hypothesis
      have ihm : Str2Int (nat_to_bit_string m) = m := ih m (by
        apply Nat.div_lt_self
        decide)
      dsimp [nat_to_bit_string]
      let rest := nat_to_bit_string m
      let bit := if k % 2 = 1 then '1' else '0'
      -- use append lemma with s2 = single-character string
      have happ := Str2Int_append rest (String.mk bit "")
      -- compute Str2Int of single-character string
      have hbit : Str2Int (String.mk bit "") = (if bit = '1' then 1 else 0) := by
        dsimp [Str2Int]
        simp
      -- combine
      have H : Str2Int (rest ++ String.mk bit "") =
               m * 2 ^ (String.mk bit "".length) + (if bit = '1' then 1 else 0) := by
        rw [happ, ihm, hbit]
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
          rw [Nat.div_mod_eq]; rfl
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