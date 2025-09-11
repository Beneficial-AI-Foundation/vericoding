namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers needed for this development.
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- strong recursion on the numeric value of the exponent (Str2Int sy)
  Nat.strongRecOn (Str2Int sy) fun m IH =>
    if m = 0 then
      -- x^0 = 1
      "1"
    else
      let (q, r) := DivMod sy "10" -- divide exponent by 2, r is "0" or "1"
      if Str2Int r = 0 then
        -- even exponent: (x^2)^(q)
        IH (Str2Int q) (by
          -- Str2Int q = m / 2 < m for m > 0
          have : Str2Int q < m := by
            -- use simple division fact: n / 2 < n for n > 0
            -- we can derive this from Nat.div_lt_self when n > 0
            apply Nat.div_lt_self
            -- m > 0 since we are in the else branch
            cases m
            · contradiction
            · simp
          exact this)
      else
        -- odd exponent: x * (x^2)^(q)
        let part := IH (Str2Int q) (by
          have : Str2Int q < m := by
            apply Nat.div_lt_self
            cases m
            · contradiction
            · simp
          exact this)
        let res := Mul part sx
        -- final reduction modulo sz
        (DivMod res sz).2
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
-- Proof by strong induction on the numeric value of the exponent Str2Int sy.
apply Nat.strongInductionOn (Str2Int sy)
intro m IH
intro hx hy hz hsy_pos hsz_gt1
by_cases hm : m = 0
-- Case m = 0: exponent is zero
· -- then ModExp returns "1"
  simp [ModExp, hm]
  constructor
  · -- "1" is a valid bitstring
    -- one-character string '1' is valid
    intros i c h
    simp at h
    cases h
    injection h with hc
    subst hc
    simp
  · -- numeric equality: 1 = x^0 % z
    simp [Str2Int, Exp_int]
    -- evaluate Str2Int "1"
    have : Str2Int "1" = 1 := by
      -- by definition foldl for "1" yields 1
      rfl
    rw [this]
    simp

-- Case m > 0
· have mpos : 0 < m := by
    have : m ≠ 0 := by
      intro H; apply hm; exact H
    cases m
    · contradiction
    · simp
  -- Unfold ModExp at this numeric value
  simp [ModExp]
  -- the `if m = 0 then ... else ...` picks the else branch
  -- compute q and r from DivMod sy "10"
  let qr := DivMod sy "10"
  let q := qr.fst
  let r := qr.snd
  have : (q, r) = DivMod sy "10" := rfl
  -- Use DivMod_spec to get correctness of q and r
  have divspec := DivMod_spec sy "10" hy (by
    -- Str2Int "10" = 2, which is > 0
    have : Str2Int "10" = 2 := by rfl
    simp [this]; linarith)
  -- destruct the conjunction from DivMod_spec
  have h_valids : ValidBitString q ∧ ValidBitString r ∧
    Str2Int q = Str2Int sy / Str2Int "10" ∧ Str2Int r = Str2Int sy % Str2Int "10" := by
    cases divspec with a b
    cases b with b1 b2
    cases b2 with b3 b4
    exact ⟨a, b1, b3, b4⟩
  have q_valid := h_valids.1
  have r_valid := h_valids.2.1
  have q_int := h_valids.2.2.1
  have r_int := h_valids.2.2.2
  -- Str2Int "10" = 2
  have two : Str2Int "10" = 2 := by rfl
  -- deduce Str2Int q = m / 2 and Str2Int r = m % 2
  have q_eq : Str2Int q
-- </vc-proof>

end BignumLean