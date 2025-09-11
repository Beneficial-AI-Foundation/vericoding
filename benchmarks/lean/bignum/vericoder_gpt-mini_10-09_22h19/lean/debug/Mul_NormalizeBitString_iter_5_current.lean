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
  induction l with
  | nil =>
    simp [List.foldl, Nat.pow, Nat.mul_one, Nat.zero_add]
  | cons hd tl ih =>
    simp [List.foldl]
    have : (2 * (acc * 2 ^ tl.length + tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
             + (if hd = '1' then 1 else 0)) =
           acc * 2 ^ (tl.length + 1) + (2 * tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
             + (if hd = '1' then 1 else 0)) := by
      simp [Nat.mul_comm, Nat.pow_succ]
      rw [Nat.mul_add, Nat.mul_comm]
    rw [this]
    simp [List.foldl]
    congr
    exact ih

-- LLM HELPER
theorem Str2Int_append (s1 s2 : String) :
  Str2Int (s1 ++ s2) = (Str2Int s1) * 2 ^ (s2.length) + Str2Int s2 := by
  have : (s1 ++ s2).data = s1.data ++ s2.data := rfl
  dsimp [Str2Int]
  conv =>
    lhs; rw [this]
  show (s1.data ++ s2.data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
       (s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 ^ s2.data.length +
         s2.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
  have h := foldl_bin s2.data (s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
  simp at h
  exact h

-- LLM HELPER
def nat_to_bit_string : Nat → String
  | 0 => "0"
  | n+1 =>
    let m := (n+1) / 2
    let rest := nat_to_bit_string m
    let bit := if (n+1) % 2 = 1 then '1' else '0'
    rest ++ String.mk bit ""
  termination_by _ n => n
  decreasing_by
    have : (n+1) / 2 < n+1 := by
      apply Nat.div_lt_self
      decide
    exact this

-- LLM HELPER
theorem nat_to_bit_string_correct : ∀ n, Str2Int (nat_to_bit_string n) = n := by
  intro n
  induction n with
  | zero => dsimp [nat_to_bit_string, Str2Int]; simp
  | succ n ih =>
    -- goal: Str2Int (nat_to_bit_string (n+1)) = n+1
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
    have : Str2Int (rest ++ String.mk bit "") =
             m * 2 ^ (String.mk bit "".length) + (if bit = '1' then 1 else 0) := by
      rw [happend, ihm, hbit]
    -- String.mk bit "" has length 1, so 2^1 = 2
    have : Str2Int (rest ++ String.mk bit "") = 2 * m + (if bit = '1' then 1 else 0) := by
      rw [this]; simp
    -- show (if bit = '1' then 1 else 0) = k % 2, using that k % 2 ∈ {0,1}
    have mod_lt := Nat.mod_lt k (by decide)
    have bit_eq_mod : (if bit = '1' then 1 else 0) = k % 2 := by
      dsimp [bit]
      let r := k % 2
      have r_lt : r < 2 := mod_lt
      cases r with
      | zero =>
        simp [r]
      | succ r' =>
        -- r = succ r' < 2, so r' = 0 and r = 1
        have : r' = 0 := by
          have : succ r' < 2 := r_lt
          linarith
        simp [this]
    -- now use Nat.div_mod_eq to finish
    calc
      Str2Int (rest ++ String.mk bit "") = 2 * m + (k % 2) := by
        rw [bit_eq_mod]
        exact this
      _ = k := by
        -- k = 2*(k/2) + k%2
        rw [Nat.div_mod_eq]
    done
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