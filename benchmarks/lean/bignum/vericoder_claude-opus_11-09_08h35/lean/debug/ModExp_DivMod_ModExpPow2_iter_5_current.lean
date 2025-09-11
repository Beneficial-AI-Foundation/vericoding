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

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    toBinary n ""

-- LLM HELPER
def IsPowerOfTwo (n : Nat) : Bool :=
  n > 0 && n.land (n - 1) = 0

-- LLM HELPER
def CountTrailingZeros (s : String) : Nat :=
  let rec count (i : Nat) : Nat :=
    if h : i < s.length then
      if s.get ⟨s.length - 1 - i, by omega⟩ = '0' then
        count (i + 1)
      else i
    else i
  count 0

-- LLM HELPER
def ModMul (sa sb sz : String) : String :=
  let prod_val := Str2Int sa * Str2Int sb
  Int2Str (prod_val % Str2Int sz)

-- LLM HELPER
lemma Int2Str_valid (n : Nat) : ValidBitString (Int2Str n) := by
  intro i c hget
  unfold Int2Str at hget
  split at hget
  · simp at hget
    cases i with
    | zero => simp at hget; left; exact hget
    | succ j => simp at hget
  · have : ∃ s, Int2Str.toBinary n "" = s := ⟨_, rfl⟩
    cases this with | intro s hs =>
    rw [← hs] at hget
    clear hs
    generalize h : Int2Str.toBinary n "" = result at hget
    induction n using Nat.strongRecOn generalizing result i with
    | ind n ih =>
      unfold Int2Str.toBinary at h
      split at h
      · simp [h] at hget
        contradiction
      · have : result = Int2Str.toBinary (n / 2) ((if n % 2 = 1 then "1" else "0") ++ "") := h
        rw [this] at hget
        clear h this
        have ih' := ih (n / 2) (Nat.div_lt_self (by omega) (by omega))
        split <;> simp at hget <;> (first | left; exact hget | right; exact hget | apply ih'; exact hget)

-- LLM HELPER  
lemma ModMul_valid (sa sb sz : String) (ha : ValidBitString sa) (hb : ValidBitString sb) (hz : ValidBitString sz) :
  ValidBitString (ModMul sa sb sz) := by
  unfold ModMul
  apply Int2Str_valid
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sy = "0" then
    "1"  -- x^0 = 1
  else if IsPowerOfTwo (Str2Int sy) then
    -- sy is a power of 2, use ModExpPow2
    let n := CountTrailingZeros sy
    ModExpPow2 sx sy n sz
  else
    -- Binary exponentiation
    let rec binExp (base : String) (exp_val : Nat) (result : String) : String :=
      if exp_val = 0 then
        result
      else
        let new_base := ModMul base base sz
        if exp_val % 2 = 1 then
          let new_result := ModMul result base sz
          binExp new_base (exp_val / 2) new_result
        else
          binExp new_base (exp_val / 2) result
    termination_by exp_val
    binExp sx (Str2Int sy) "1"
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
  · -- Case: sy = "0"
    next h0 =>
    simp [h0, Str2Int, Exp_int]
    constructor
    · intro i c hget
      simp at hget
      cases i with
      | zero => simp at hget; left; exact hget
      | succ j => simp at hget
    · norm_num
      rfl
  · split
    · -- Case: IsPowerOfTwo (Str2Int sy)
      next h1 =>
      have hpow2_or_zero : Str2Int sy = Exp_int 2 (CountTrailingZeros sy) ∨ Str2Int sy = 0 := by
        left
        unfold IsPowerOfTwo at h1
        simp at h1
        have ⟨hp, _⟩ := h1
        generalize hn : Str2Int sy = n at hp h1
        clear hn sx sz hx hz hsz_gt1 hsy_pos sy hy
        induction n using Nat.strongRecOn with
        | ind n ih =>
          unfold CountTrailingZeros CountTrailingZeros.count
          unfold Exp_int
          split
          · rfl
          · simp
            split
            · simp
              split <;> simp [Exp_int]
            · simp [Exp_int]
      have hlen : sy.length = CountTrailingZeros sy + 1 := by
        unfold CountTrailingZeros CountTrailingZeros.count
        simp
        generalize hs : sy = s
        clear hs
        induction s with
        | nil => simp
        | cons c cs ih => simp
      exact ModExpPow2_spec sx sy (CountTrailingZeros sy) sz hx hy hz hpow2_or_zero hlen hsz_gt1
    · -- Case: General binary exponentiation
      next h2 =>
      have hbinExp : ∀ b ev r, ValidBitString b → ValidBitString r → 
        ValidBitString (ModExp.binExp sz b ev r) ∧
        Str2Int (ModExp.binExp sz b ev r) = (Exp_int (Str2Int b) ev * Str2Int r) % Str2Int sz := by
        intro b ev
        induction ev using Nat.strongRecOn with
        | ind ev ih =>
          intro r hb hr
          unfold ModExp.binExp
          split
          · simp [Exp_int]
            exact ⟨hr, by ring_nf⟩
          · next hev =>
            have hmod := ModMul_valid b b sz hb hb hz
            split
            · have hmod2 := ModMul_valid r b sz hr hb hz
              have ih' := ih (ev / 2) (Nat.div_lt_self (by omega) (by omega)) _ hmod hmod2
              constructor
              · exact ih'.1
              · rw [ih'.2]
                unfold ModMul Exp_int
                split
                · contradiction
                · simp [Str2Int]
                  have : ev = 2 * (ev / 2) + 1 := by omega
                  rw [this]
                  ring_nf
                  have h1 : Exp_int (Str2Int b) (2 * (ev / 2)) = 
                           Exp_int (Str2Int b * Str2Int b) (ev / 2) := by
                    clear this ih ih' hmod hmod2 h2 hev
                    generalize hb' : Str2Int b = b'
                    generalize hev' : ev / 2 = ev'
                    clear hb' hev' b ev hb hr r
                    induction ev' with
                    | zero => simp [Exp_int]
                    | succ n ih =>
                      simp [Exp_int, Nat.mul_succ]
                      ring_nf
                      rw [← ih]
                      ring
                  rw [h1]
                  ring_nf
                  rw [Nat.mul_mod, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
                  ring_nf
                  rw [← Nat.mul_mod, ← Nat.mul_mod]
                  ring_nf
                  intro h
                  omega
            · have ih' := ih (ev / 2) (Nat.div_lt_self (by omega) (by omega)) r hmod hr
              constructor
              · exact ih'.1
              · rw [ih'.2]
                unfold ModMul Exp_int
                split
                · contradiction  
                · simp [Str2Int]
                  have : ev = 2 * (ev / 2) := by omega
                  rw [this]
                  have h1 : Exp_int (Str2Int b) (2 * (ev / 2)) = 
                           Exp_int (Str2Int b * Str2Int b) (ev / 2) := by
                    generalize hb' : Str2Int b = b'
                    generalize hev' : ev / 2 = ev'
                    clear this ih ih' hmod h2 hev hb' hev' b ev hb hr r
                    induction ev' with
                    | zero => simp [Exp_int]
                    | succ n ih =>
                      simp [Exp_int, Nat.mul_succ]
                      ring_nf
                      rw [← ih]
                      ring
                  rw [h1]
                  ring_nf
                  rw [Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
                  ring_nf
                  intro h
                  omega
      have h1valid : ValidBitString "1" := by
        intro i c hget
        simp at hget
        cases i with
        | zero => simp at hget; left; exact hget
        | succ j => simp at hget
      have ⟨hvalid, hval⟩ := hbinExp sx (Str2Int sy) "1" hx h1valid
      constructor
      · exact hvalid
      · simp [Str2Int] at hval
        exact hval
-- </vc-proof>

end BignumLean