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
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    let bit := (if hd = '1' then 1 else 0)
    have H := ih (2 * acc + bit)
    have H0 := ih bit
    -- From H: foldl f (2*acc+bit) tl = (2*acc+bit) * 2^tl.length + foldl f 0 tl
    -- Now algebraically manipulate to the desired form
    calc
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * acc + bit) tl
        = (2 * acc + bit) * 2 ^ tl.length + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tl := by
          exact H
      _ = (2 * acc) * 2 ^ tl.length + bit * 2 ^ tl.length + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tl := by
          -- distribute multiplication over addition
          rw [Nat.mul_add]
      _ = acc * (2 * 2 ^ tl.length) + (bit * 2 ^ tl.length + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tl) := by
          -- rearrange (2*acc) * 2^tl.length into acc * (2 * 2^tl.length)
          calc
            (2 * acc) * 2 ^ tl.length = 2 * (acc * 2 ^ tl.length) := by
              rw [Nat.mul_assoc]
            _ = acc * (2 * 2 ^ tl.length) := by
              -- 2 * (acc * 2 ^ tl.length) = acc * (2 * 2 ^ tl.length)
              rw [Nat.mul_comm 2 (acc * 2 ^ tl.length)]
              rw [Nat.mul_assoc]
      _ = acc * 2 ^ (tl.length + 1) + (bit * 2 ^ tl.length + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tl) := by
          rw [Nat.pow_succ]
      _ = acc * 2 ^ (tl.length + 1) + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) bit tl := by
          -- use H0 to replace the last part
          rw [←H0]; rfl

-- LLM HELPER
theorem Str2Int_append (s1 s2 : String) :
  Str2Int (s1 ++ s2) = (Str2Int s1) * 2 ^ (s2.length) + Str2Int s2 := by
  dsimp [Str2Int]
  -- (s1 ++ s2).data = s1.data ++ s2.data
  have hdata : (s1 ++ s2).data = s1.data ++ s2.data := rfl
  rw [hdata]
  -- foldl on appended lists: foldl f 0 (xs ++ ys) = foldl f (foldl f 0 xs) ys
  have happend : (s1.data ++ s2.data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
                 s2.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
    exact List.foldl_append _ _ _ _
  rw [happend]
  -- apply foldl_bin to s2.data with acc = Str2Int s1
  have H := foldl_bin s2.data (s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
  -- simplify to the desired form
  dsimp [Str2Int] at H
  -- H states: s2.data.foldl f (Str2Int s1) = Str2Int s1 * 2 ^ s2.data.length + s2.data.foldl f 0
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
    -- show (n+1)/2 < n+1 using divisor 2 > 1
    have : (n + 1) / 2 < n + 1 := by
      apply Nat.div_lt_self
      decide
    exact this

-- LLM HELPER
theorem nat_to_bit_string_correct : ∀ n, Str2Int (nat_to_bit_string n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n with
    | zero => simp [nat_to_bit_string, Str2Int]
    | succ n' =>
      let k := n' + 1
      let m := k / 2
      -- m < k, so we can use strong induction hypothesis
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
        -- underlying data is [bit]
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
          -- k = 2*(k/2) + k%2
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