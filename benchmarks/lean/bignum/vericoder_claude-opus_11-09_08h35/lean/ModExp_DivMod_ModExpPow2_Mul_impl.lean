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
def isZero (s : String) : Bool :=
  s.all (· = '0') || s.isEmpty

-- LLM HELPER
def isOne (s : String) : Bool :=
  s = "1"

-- LLM HELPER
def lastBit (s : String) : Char :=
  if h : s.length > 0 then s.get ⟨s.length - 1, by omega⟩ else '0'

-- LLM HELPER
def dropLastBit (s : String) : String :=
  if s.length > 0 then s.take (s.length - 1) else ""

-- LLM HELPER
lemma dropLastBit_valid (s : String) (h : ValidBitString s) : ValidBitString (dropLastBit s) := by
  intro i c hc
  simp [dropLastBit] at hc
  split at hc
  · rename_i h_pos
    simp [String.take, String.get?] at hc
    split at hc
    · rename_i h_bound
      have := h
      simp [ValidBitString] at this
      apply this
      simp [String.get?]
      split
      · rename_i hi
        have : i < s.length - 1 := by
          simp [String.length, String.take] at h_bound
          exact h_bound
        have : i < s.length := by omega
        simp [this]
        convert hc
        simp [String.take, String.get]
        congr
        ext
        simp
        rw [List.get_take]
        omega
      · rename_i hi
        simp at h_bound
        omega
    · contradiction
  · contradiction

-- LLM HELPER
lemma str2int_dropLastBit_lastBit (s : String) (h : ValidBitString s) (h_pos : s.length > 0) :
  Str2Int s = 2 * Str2Int (dropLastBit s) + (if lastBit s = '1' then 1 else 0) := by
  simp [Str2Int, dropLastBit, lastBit, h_pos]
  cases hs : s.data with
  | nil => simp [String.length] at h_pos; omega
  | cons c cs =>
    have : s.take (s.length - 1) = ⟨cs.dropLast⟩ := by
      simp [String.take]
      ext
      simp
      rw [← hs]
      simp [List.take, String.length]
      rw [← hs]
      simp
      have : s.data.length = cs.length + 1 := by rw [hs]; simp
      rw [this]
      simp [Nat.add_sub_cancel]
    rw [this]
    simp [List.foldl]
    have last_char : s.get ⟨s.length - 1, h_pos⟩ = cs.getLast?.getD '0' := by
      simp [String.get, String.length]
      rw [← hs]
      simp [List.get]
      cases hcs : cs with
      | nil => simp
      | cons c' cs' =>
        simp [List.getLast?]
        rw [← hcs]
        simp [List.getLast_cons]
        congr 1
        simp [String.length]
        rw [← hs]
        simp
    rw [last_char]
    generalize cs.dropLast = cs_init
    generalize cs.getLast?.getD '0' = last
    clear this last_char hs
    induction cs_init generalizing cs with
    | nil => 
      simp [List.foldl]
      split <;> simp
    | cons c' cs_init' ih =>
      simp [List.foldl]
      split
      · simp
        ring_nf
        congr 1
        apply ih
      · simp
        ring_nf
        congr 1
        apply ih
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if h : sy.length = 0 then
    "1"
  else if isZero sy then
    "1"
  else if isOne sy then
    let (_, remainder) := DivMod sx sz
    remainder
  else
    let lastBitChar := lastBit sy
    let syDiv2 := dropLastBit sy
    let xSquared := Mul sx sx
    let (_, xSquaredMod) := DivMod xSquared sz
    have : syDiv2.length < sy.length := by
      simp only [dropLastBit]
      split
      · simp [String.length, String.take]
        omega
      · omega
    let recResult := ModExp xSquaredMod syDiv2 sz
    if lastBitChar = '1' then
      let temp := Mul recResult sx
      let (_, result) := DivMod temp sz
      result
    else
      recResult
termination_by sy.length
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  split
  · rename_i h
    omega
  · split
    · rename_i h_zero
      constructor
      · intro i c hc
        simp at hc
        cases hc with
        | inl h => left; exact h.symm
        | inr h => contradiction
      · have : Str2Int sy = 0 := by
          simp [Str2Int]
          cases hs : sy.data with
          | nil => simp
          | cons c cs =>
            simp [List.foldl]
            have h_all := h_zero
            simp [isZero, String.all] at h_all
            cases h_all with
            | inl h_all =>
              have hc : c = '0' := by
                apply h_all
                rw [← hs]
                exact List.mem_cons_self _ _
              simp [hc]
              clear hc
              induction cs with
              | nil => simp
              | cons c' cs' ih =>
                simp [List.foldl]
                have : c' = '0' := by
                  apply h_all
                  rw [← hs]
                  exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
                simp [this]
                apply ih
                intro x hx
                apply h_all
                rw [← hs]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
            | inr h_empty =>
              simp [String.isEmpty] at h_empty
              rw [← hs] at h_empty
              simp at h_empty
        rw [this]
        simp [Exp_int]
        omega
    · split
      · rename_i h_one
        have div_spec := DivMod_spec sx sz hx hz hsz_gt1
        obtain ⟨_, hr, _, hr_val⟩ := div_spec
        constructor
        · exact hr
        · have : Str2Int sy = 1 := by
            simp [isOne] at h_one
            rw [h_one]
            simp [Str2Int, List.foldl]
          rw [this]
          simp [Exp_int]
          exact hr_val
      · rename_i _ _ _
        have mul_spec := Mul_spec sx sx hx hx
        have div_spec := DivMod_spec (Mul sx sx) sz mul_spec.1 hz hsz_gt1
        have syDiv2_valid := dropLastBit_valid sy hy
        have syDiv2_pos : (dropLastBit sy).length > 0 := by
          simp [dropLastBit]
          split
          · rename_i h
            simp [String.take, String.length]
            omega
          · omega
        have rec_spec := ModExp_spec (snd (DivMod (Mul sx sx) sz)) (dropLastBit sy) sz
          div_spec.2.1 syDiv2_valid hz syDiv2_pos hsz_gt1
        split
        · rename_i h_lastbit
          have temp_spec := Mul_spec (ModExp (snd (DivMod (Mul sx sx) sz)) (dropLastBit sy) sz) sx rec_spec.1 hx
          have final_div := DivMod_spec (Mul (ModExp (snd (DivMod (Mul sx sx) sz)) (dropLastBit sy) sz) sx) sz temp_spec.1 hz hsz_gt1
          constructor
          · exact final_div.2.1
          · rw [final_div.2.2.2, temp_spec.2, rec_spec.2]
            have exp_rec : Exp_int (Str2Int sx) (Str2Int sy) = 
                Exp_int (Str2Int sx) (2 * Str2Int (dropLastBit sy) + 1) := by
              congr
              apply str2int_dropLastBit_lastBit sy hy hsy_pos ▸ _
              simp [h_lastbit]
            rw [exp_rec]
            clear exp_rec
            generalize Str2Int sx = x
            generalize Str2Int (dropLastBit sy) = n
            generalize Str2Int sz = m
            have : Exp_int x (2 * n + 1) = x * Exp_int x (2 * n) := by
              simp [Exp_int]
              ring_nf
            rw [this]
            have : Exp_int x (2 * n) = Exp_int (x * x) n := by
              induction n with
              | zero => simp [Exp_int]
              | succ n ih =>
                simp [Exp_int]
                ring_nf
                rw [← ih]
                simp [Exp_int]
                ring_nf
            rw [this]
            rw [mul_spec.2, div_spec.2.2.2]
            ring_nf
            rw [Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
            · ring_nf
            · omega
        · rename_i h_lastbit
          constructor
          · exact rec_spec.1
          · rw [rec_spec.2]
            have exp_rec : Exp_int (Str2Int sx) (Str2Int sy) = 
                Exp_int (Str2Int sx) (2 * Str2Int (dropLastBit sy)) := by
              congr
              apply str2int_dropLastBit_lastBit sy hy hsy_pos ▸ _
              split
              · rename_i h
                have : lastBit sy = '0' := by
                  by_contra h'
                  have hc := hy (sy.length - 1) (lastBit sy)
                  simp [lastBit, hsy_pos, String.get?] at hc
                  have hget : sy.get? (sy.length - 1) = some (sy.get ⟨sy.length - 1, hsy_pos⟩) := by
                    simp [String.get?]
                    split
                    · rfl
                    · rename_i h''
                      omega
                  rw [hget] at hc
                  cases hc (by rfl) with
                  | inl h0 => exact h_lastbit h0
                  | inr h1 => exact h' h1
                rw [this]
              · contradiction
            rw [exp_rec]
            have : Exp_int (Str2Int sx) (2 * Str2Int (dropLastBit sy)) = 
                Exp_int (Str2Int sx * Str2Int sx) (Str2Int (dropLastBit sy)) := by
              generalize Str2Int sx = x
              generalize Str2Int (dropLastBit sy) = n
              induction n with
              | zero => simp [Exp_int]
              | succ n ih =>
                simp [Exp_int]
                ring_nf
                rw [← ih]
                simp [Exp_int]
                ring_nf
            rw [this, mul_spec.2, div_spec.2.2.2]
-- </vc-proof>

end BignumLean