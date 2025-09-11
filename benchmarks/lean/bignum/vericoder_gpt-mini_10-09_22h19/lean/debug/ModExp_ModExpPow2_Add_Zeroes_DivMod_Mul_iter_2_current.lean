namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
-- Basic lemmas about string concatenation and simple constants used in ModExp proof.

open String

lemma one_valid : ValidBitString "1" := by
  intros i c h
  simp only [get?] at h
  -- "1" has length 1, so only index 0 can produce some char
  have : "1".length = 1 := by rfl
  -- use the fact that the only character is '1'
  simp [this] at h
  injection h with hc
  rw [hc]; simp; tauto

-- Lemma: For any string s and any z which is all zeros (AllZero z),
-- Str2Int (s ++ z) = Str2Int s * Exp_int 2 (z.length).
-- We prove this by induction on z.length using the behaviour of foldl.
lemma Str2Int_append_zeros {s z : String} (hz : AllZero z) :
  Str2Int (s ++ z) = Str2Int s * Exp_int 2 (z.length) := by
  -- We'll prove by induction on z.length.
  have : ∀ k, z.length = k → Str2Int (s ++ z) = Str2Int s * Exp_int 2 k := by
    intro k hk
    induction k with
    | zero =>
      have : z.length = 0 := hk
      -- z is empty
      have z_empty : z = "" := by
        -- A string of length 0 is the empty string
        have := congrArg (fun t => t.length) (rfl : z = z)
        simp [this, hk] at *
        rfl
      simp [z_empty]
    | succ k ih =>
      -- z has length k+1. Use that all characters of z are '0'. In particular,
      -- the first character is '0' and the rest has AllZero and length k.
      -- We will decompose z into c :: ztail by using get? at index 0 and substring.
      have hzlen : z.length = k + 1 := hk
      -- Obtain first character and tail via get? and substring operations
      cases z.get? 0 with
      | none =>
        -- impossible since length >=1
        simp at hzlen; contradiction
      | some c =>
        have hc : c = '0' := (hz (0) c (by simp [*])) 
        -- obtain tail as substring from 1 to end
        let ztail := z.drop 1
        have ztail_len : ztail.length = k := by
          -- length drop property
          simp [drop]; -- `drop` definition is reducible enough for this goal
          exact by
            -- because z.length = k+1, dropping 1 yields k
            simp [hzlen]
        -- prove AllZero for ztail
        have hztail : AllZero ztail := by
          intro i ch hget
          -- get? on ztail corresponds to get? on z at position i+1
          have : z.get? (i + 1) = some ch := by
            -- definition of drop/get? interplay
            simp [drop] at hget
            exact hget
          specialize hz (i + 1) ch this
          exact hz
        -- Now reason about Str2Int (s ++ z) = Str2Int ( (s ++ String.singleton c) ++ ztail )
        have : s ++ z = (s ++ String.singleton c) ++ ztail := by
          simp [drop]; -- just re-associate append
        simp [this]
        -- compute for the last zero: appending a '0' at the end multiplies numeric value by 2
        -- So Str2Int ((s ++ String.singleton c) ++ ztail) = (Str2Int (s ++ String.singleton c)) * Exp_int 2 k
        have ih_apply : Str2Int ((s ++ String.singleton c) ++ ztail) = Str2Int (s ++ String.singleton c) * Exp_int 2 k := by
          apply ih
          simp [ztail_len]
        -- compute Str2Int (s ++ String.singleton c) when c = '0' and s arbitrary:
        -- Str2Int (s ++ "0") = 2 * Str2Int s
        have step : Str2Int (s ++ String.singleton c) = 2 * Str2Int s := by
          -- When appending '0', foldl will multiply accumulator by 2 and add 0.
          -- So numeric effect is multiply by 2.
          -- We can reason by unfolding definitions to reduce to rfl.
          -- We use the fact c = '0'.
          have : String.singleton c = "0" := by
            simp [hc]; rfl
          simp [this]
          -- now the result follows by definition of Str2Int (folding a trailing '0')
          -- Lean's evaluation does the rest
        -- combine:
        calc
          Str2Int (s ++ z) = Str
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
-- Basic lemmas about string concatenation and simple constants used in ModExp proof.

open String

lemma one_valid : ValidBitString "1" := by
  intros i c h
  simp only [get?] at h
  -- "1" has length 1, so only index 0 can produce some char
  have : "1".length = 1 := by rfl
  -- use the fact that the only character is '1'
  simp [this] at h
  injection h with hc
  rw [hc]; simp; tauto

-- Lemma: For any string s and any z which is all zeros (AllZero z),
-- Str2Int (s ++ z) = Str2Int s * Exp_int 2 (z.length).
-- We prove this by induction on z.length using the behaviour of foldl.
lemma Str2Int_append_zeros {s z : String} (hz : AllZero z) :
  Str2Int (s ++ z) = Str2Int s * Exp_int 2 (z.length) := by
  -- We'll prove by induction on z.length.
  have : ∀ k, z.length = k → Str2Int (s ++ z) = Str2Int s * Exp_int 2 k := by
    intro k hk
    induction k with
    | zero =>
      have : z.length = 0 := hk
      -- z is empty
      have z_empty : z = "" := by
        -- A string of length 0 is the empty string
        have := congrArg (fun t => t.length) (rfl : z = z)
        simp [this, hk] at *
        rfl
      simp [z_empty]
    | succ k ih =>
      -- z has length k+1. Use that all characters of z are '0'. In particular,
      -- the first character is '0' and the rest has AllZero and length k.
      -- We will decompose z into c :: ztail by using get? at index 0 and substring.
      have hzlen : z.length = k + 1 := hk
      -- Obtain first character and tail via get? and substring operations
      cases z.get? 0 with
      | none =>
        -- impossible since length >=1
        simp at hzlen; contradiction
      | some c =>
        have hc : c = '0' := (hz (0) c (by simp [*])) 
        -- obtain tail as substring from 1 to end
        let ztail := z.drop 1
        have ztail_len : ztail.length = k := by
          -- length drop property
          simp [drop]; -- `drop` definition is reducible enough for this goal
          exact by
            -- because z.length = k+1, dropping 1 yields k
            simp [hzlen]
        -- prove AllZero for ztail
        have hztail : AllZero ztail := by
          intro i ch hget
          -- get? on ztail corresponds to get? on z at position i+1
          have : z.get? (i + 1) = some ch := by
            -- definition of drop/get? interplay
            simp [drop] at hget
            exact hget
          specialize hz (i + 1) ch this
          exact hz
        -- Now reason about Str2Int (s ++ z) = Str2Int ( (s ++ String.singleton c) ++ ztail )
        have : s ++ z = (s ++ String.singleton c) ++ ztail := by
          simp [drop]; -- just re-associate append
        simp [this]
        -- compute for the last zero: appending a '0' at the end multiplies numeric value by 2
        -- So Str2Int ((s ++ String.singleton c) ++ ztail) = (Str2Int (s ++ String.singleton c)) * Exp_int 2 k
        have ih_apply : Str2Int ((s ++ String.singleton c) ++ ztail) = Str2Int (s ++ String.singleton c) * Exp_int 2 k := by
          apply ih
          simp [ztail_len]
        -- compute Str2Int (s ++ String.singleton c) when c = '0' and s arbitrary:
        -- Str2Int (s ++ "0") = 2 * Str2Int s
        have step : Str2Int (s ++ String.singleton c) = 2 * Str2Int s := by
          -- When appending '0', foldl will multiply accumulator by 2 and add 0.
          -- So numeric effect is multiply by 2.
          -- We can reason by unfolding definitions to reduce to rfl.
          -- We use the fact c = '0'.
          have : String.singleton c = "0" := by
            simp [hc]; rfl
          simp [this]
          -- now the result follows by definition of Str2Int (folding a trailing '0')
          -- Lean's evaluation does the rest
        -- combine:
        calc
          Str2Int (s ++ z) = Str
-- </vc-code>

end BignumLean