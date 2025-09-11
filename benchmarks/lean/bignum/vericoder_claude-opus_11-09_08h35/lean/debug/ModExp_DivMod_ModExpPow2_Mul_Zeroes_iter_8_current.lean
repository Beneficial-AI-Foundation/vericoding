namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

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

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def getBit (s : String) (i : Nat) : Bool :=
  match s.data[i]? with
  | some '1' => true
  | _ => false

-- LLM HELPER
def isAllZero (s : String) : Bool :=
  s.data.all (· = '0')

-- LLM HELPER
def isPowerOfTwo (s : String) : Bool :=
  let nonZeroCount := s.data.filter (· = '1') |>.length
  nonZeroCount = 1

-- LLM HELPER
def getPowerOfTwo (s : String) : Nat :=
  s.data.reverse.foldl (fun (acc : Nat × Nat) c => 
    let (idx, result) := acc
    if c = '1' then (idx + 1, idx) else (idx + 1, result)) (0, 0) |>.2

-- LLM HELPER
def modExpBinary (base exp modulus : String) (idx : Nat) (result : String) : String :=
  if idx = 0 then
    result
  else
    let idx' := idx - 1
    let result' := if getBit exp idx' then
      let temp := Mul result base
      (DivMod temp modulus).2
    else
      result
    if idx' = 0 then
      result'
    else
      let base' := Mul base base
      let base'' := (DivMod base' modulus).2
      modExpBinary base'' exp modulus idx' result'
termination_by idx

-- LLM HELPER
lemma isAllZero_implies_str2int_zero (s : String) (h : isAllZero s = true) : Str2Int s = 0 := by
  unfold Str2Int isAllZero at *
  have : ∀ c ∈ s.data, c = '0' := List.all_iff_forall.mp h
  induction s.data with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.foldl]
    have hd_eq : hd = '0' := this hd (List.mem_cons_self hd tl)
    simp [hd_eq]
    have tl_prop : ∀ c ∈ tl, c = '0' := fun c hc => this c (List.mem_cons_of_mem hd hc)
    exact ih tl_prop

-- LLM HELPER  
lemma one_valid : ValidBitString "1" := by
  unfold ValidBitString
  intro i c h
  unfold String.get? at h
  cases h' : "1".data[i]? with
  | none => simp [h'] at h
  | some c' =>
    simp [h'] at h
    cases i with
    | zero => 
      simp at h'
      simp [← h, h']
      right; rfl
    | succ n => 
      simp at h'

-- LLM HELPER
lemma one_str2int : Str2Int "1" = 1 := by
  unfold Str2Int
  simp [List.foldl]

-- LLM HELPER
lemma modExpBinary_valid (base exp modulus : String) (idx : Nat) (result : String)
  (hbase : ValidBitString base) (hexp : ValidBitString exp) (hmod : ValidBitString modulus)
  (hresult : ValidBitString result) (hmod_gt1 : Str2Int modulus > 1) :
  ValidBitString (modExpBinary base exp modulus idx result) := by
  induction idx generalizing base result with
  | zero => simp [modExpBinary]; exact hresult
  | succ n ih =>
    simp [modExpBinary]
    by_cases h : n = 0
    · simp [h, modExpBinary]
      by_cases h2 : getBit exp 0
      · have h1 := Mul_spec result base hresult hbase
        have h2 := DivMod_spec (Mul result base) modulus h1.1 hmod hmod_gt1
        exact h2.2.1
      · exact hresult
    · simp [h]
      by_cases h2 : getBit exp n
      · have h1 := Mul_spec result base hresult hbase
        have h2 := DivMod_spec (Mul result base) modulus h1.1 hmod hmod_gt1
        have h3 := Mul_spec base base hbase hbase
        have h4 := DivMod_spec (Mul base base) modulus h3.1 hmod hmod_gt1
        apply ih h4.2.1 h2.2.1
      · have h3 := Mul_spec base base hbase hbase
        have h4 := DivMod_spec (Mul base base) modulus h3.1 hmod hmod_gt1
        apply ih h4.2.1 hresult

-- LLM HELPER
lemma modExpBinary_correct (base exp modulus : String) (idx : Nat) (result : String)
  (hbase : ValidBitString base) (hexp : ValidBitString exp) (hmod : ValidBitString modulus)
  (hresult : ValidBitString result) (hmod_gt1 : Str2Int modulus > 1) :
  Str2Int (modExpBinary base exp modulus idx result) = 
    (Str2Int result * Exp_int (Str2Int base) (Str2Int exp % (2^idx))) % Str2Int modulus := by
  induction idx generalizing base result with
  | zero => 
    simp [modExpBinary, Exp_int, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    simp [modExpBinary]
    by_cases h : n = 0
    · simp [h, modExpBinary]
      by_cases h2 : getBit exp 0
      · have h1 := Mul_spec result base hresult hbase
        have h2' := DivMod_spec (Mul result base) modulus h1.1 hmod hmod_gt1
        simp [h2'.2.2.2, h1.2]
        simp [Exp_int, Nat.pow_one]
        ring_nf
      · simp [Exp_int, Nat.pow_one]
    · simp [h]
      by_cases h2 : getBit exp n
      · have h1 := Mul_spec result base hresult hbase
        have h2' := DivMod_spec (Mul result base) modulus h1.1 hmod hmod_gt1
        have h3 := Mul_spec base base hbase hbase
        have h4 := DivMod_spec (Mul base base) modulus h3.1 hmod hmod_gt1
        rw [ih h4.2.1 h2'.2.1]
        simp [h2'.2.2.2, h4.2.2.2, h1.2, h3.2]
        ring_nf
      · have h3 := Mul_spec base base hbase hbase
        have h4 := DivMod_spec (Mul base base) modulus h3.1 hmod hmod_gt1
        rw [ih h4.2.1 hresult]
        simp [h4.2.2.2, h3.2]
        ring_nf
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if isAllZero sy then
    -- y = 0, so x^0 = 1
    let one := "1"
    (DivMod one sz).2
  else if isPowerOfTwo sy then
    -- y is a power of 2, use ModExpPow2
    let n := getPowerOfTwo sy
    ModExpPow2 sx sy n sz
  else
    -- General case: use binary exponentiation
    let one := "1"
    let result_init := (DivMod one sz).2
    modExpBinary sx sy sz sy.length result_init
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  by_cases h1 : isAllZero sy
  · -- Case: sy is all zeros (y = 0)
    simp [h1]
    have h_sy_zero : Str2Int sy = 0 := isAllZero_implies_str2int_zero sy h1
    simp [h_sy_zero, Exp_int]
    obtain ⟨hq, hr, hq_val, hr_val⟩ := DivMod_spec "1" sz one_valid hz hsz_gt1
    constructor
    · exact hr
    · simp [hr_val, one_str2int]
      exact Nat.mod_eq_of_lt hsz_gt1
  · simp [h1]
    by_cases h2 : isPowerOfTwo sy
    · -- Case: sy is a power of 2
      simp [h2]
      let n := getPowerOfTwo sy
      have h3 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0 := by
        left
        exact calc Str2Int sy = 2^n := by rfl
          _ = Exp_int 2 n := by rfl
      have h4 : sy.length = n + 1 := by rfl
      exact ModExpPow2_spec sx sy n sz hx hy hz h3 h4 hsz_gt1
    · -- General case with binary exponentiation
      simp [h2]
      have h3 := DivMod_spec "1" sz one_valid hz hsz_gt1
      have hres_valid := h3.2.1
      constructor
      · apply modExpBinary_valid sx sy sz sy.length (DivMod "1" sz).2 hx hy hz hres_valid hsz_gt1
      · simp [h3.2.2.2, one_str2int]
        have h4 := modExpBinary_correct sx sy sz sy.length "1" hx hy hz one_valid hsz_gt1
        simp [one_str2int] at h4
        simp [Nat.mod_eq_of_lt hsz_gt1] at h4
        exact calc Str2Int (modExpBinary sx sy sz sy.length (DivMod "1" sz).2)
          = (1 * Exp_int (Str2Int sx) (Str2Int sy % (2^sy.length))) % Str2Int sz := by
            rw [h3.2.2.2, one_str2int] at h4
            simp [Nat.mod_eq_of_lt hsz_gt1] at h4
            exact h4
          _ = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
            simp
            congr
            have : Str2Int sy < 2^sy.length := by rfl
            exact Nat.mod_eq_of_lt this
-- </vc-proof>

end BignumLean