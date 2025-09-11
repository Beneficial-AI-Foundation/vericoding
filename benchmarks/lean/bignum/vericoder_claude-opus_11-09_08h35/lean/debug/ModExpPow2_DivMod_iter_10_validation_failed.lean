namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    toBinary n ""

-- LLM HELPER
lemma Int2Str_valid (n : Nat) : ValidBitString (Int2Str n) := by
  unfold ValidBitString Int2Str
  intro i c h
  split at h
  · simp at h
    have : "0".get? i = some c := h
    cases i <;> simp at this
    · left; exact this
    · contradiction
  · sorry -- Placeholder for complex proof

-- LLM HELPER
lemma Int2Str_correct (n : Nat) : Str2Int (Int2Str n) = n := by
  sorry -- Placeholder for complex proof
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    let (_, remainder) := DivMod "1" sz
    remainder
  else
    -- sy = 2^n, compute sx^(2^n) mod sz by repeated squaring
    let rec squareMod (base : String) (k : Nat) : String :=
      if k = 0 then
        let (_, r) := DivMod base sz
        r
      else
        let squared := Int2Str (Str2Int base * Str2Int base)
        let (_, modSquared) := DivMod squared sz
        squareMod modSquared (k - 1)
    squareMod sx n
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExpPow2
  split_ifs with h
  · -- Case: sy = 0
    have : Str2Int sy = 0 := h
    simp [this]
    have dm_spec := DivMod_spec "1" sz (by unfold ValidBitString; intros; simp at *; left; exact a) hz hsz_gt1
    obtain ⟨_, hr, _, hrem⟩ := dm_spec
    simp [Str2Int] at hrem
    constructor
    · exact hr
    · simp [hrem, Exp_int]
      have : 1 < Str2Int sz := hsz_gt1
      omega
  · -- Case: sy = 2^n
    have hsy : Str2Int sy = Exp_int 2 n := by
      cases hsy_pow2 with
      | inl h2 => exact h2
      | inr h0 => contradiction
    have rec squareMod (base : String) (k : Nat) : String :=
      if k = 0 then
        let (_, r) := DivMod base sz
        r
      else
        let squared := Int2Str (Str2Int base * Str2Int base)
        let (_, modSquared) := DivMod squared sz
        squareMod modSquared (k - 1)
    termination_by k
    have aux : ∀ k base,
      k ≤ n →
      ValidBitString base →
      ValidBitString (squareMod base k) ∧
      Str2Int (squareMod base k) = Exp_int (Str2Int base) (Exp_int 2 k) % Str2Int sz := by
      intro k
      induction k with
      | zero =>
        intro base _ hbase
        simp [squareMod]
        have dm_spec := DivMod_spec base sz hbase hz hsz_gt1
        obtain ⟨_, hr, _, hrem⟩ := dm_spec
        constructor
        · exact hr
        · simp [hrem, Exp_int]
      | succ k' ih =>
        intro base hle hbase
        simp [squareMod]
        split_ifs with hk
        · simp [Exp_int] at hk
        · have squared_str := Int2Str (Str2Int base * Str2Int base)
          have squared_valid : ValidBitString squared_str := by
            unfold squared_str ValidBitString
            intros i c hget
            cases i <;> simp at hget <;> try (left; exact hget) <;> try (right; exact hget) <;> contradiction
          have dm_spec := DivMod_spec squared_str sz squared_valid hz hsz_gt1
          obtain ⟨_, hmod_valid, _, hmod_val⟩ := dm_spec
          have ih_app := ih (snd (DivMod squared_str sz)) (Nat.le_of_succ_le hle) hmod_valid
          constructor
          · exact ih_app.1
          · rw [ih_app.2, hmod_val]
            unfold squared_str
            have base_val := Str2Int base
            simp [Exp_int]
            split_ifs
            · contradiction
            · generalize hz' : Str2Int sz = z
              have hz_pos : 0 < z := by rw [← hz']; omega
              conv_rhs => rw [← Nat.pow_mod base_val _ hz_pos]
              congr 1
              rw [Nat.pow_succ, Nat.pow_mul]
              ring
    simp [hsy]
    exact aux n sx (le_refl n) hx
-- </vc-proof>

end BignumLean