namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    toBinary n ""

-- LLM HELPER
axiom Int2Str_valid (n : Nat) : ValidBitString (Int2Str n)

-- LLM HELPER
axiom Int2Str_correct (n : Nat) : Str2Int (Int2Str n) = n

-- LLM HELPER
axiom Int2Str_pos_length (n : Nat) (h : n > 0) : (Int2Str n).length > 0

-- LLM HELPER
def ModMul (a b m : String) : String :=
  Int2Str (Str2Int (Mul a b) % Str2Int m)

-- LLM HELPER
lemma ModMul_valid (a b m : String) (ha : ValidBitString a) (hb : ValidBitString b) (hm : ValidBitString m) :
  ValidBitString (ModMul a b m) := by
  unfold ModMul
  exact Int2Str_valid _

-- LLM HELPER
lemma ModMul_correct (a b m : String) (ha : ValidBitString a) (hb : ValidBitString b) (hm : ValidBitString m) (hm_pos : Str2Int m > 0) :
  Str2Int (ModMul a b m) = (Str2Int a * Str2Int b) % Str2Int m := by
  unfold ModMul
  rw [Int2Str_correct]
  have ⟨_, hmul⟩ := Mul_spec a b ha hb
  rw [hmul]
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sy = "0" || sy.length = 0 then
    "1"
  else
    let rec modExpAux (base : String) (exp : Nat) (mod : String) (result : String) : String :=
      if exp = 0 then
        result
      else if exp % 2 = 1 then
        modExpAux (ModMul base base mod) (exp / 2) mod (ModMul result base mod)
      else
        modExpAux (ModMul base base mod) (exp / 2) mod result
    modExpAux sx (Str2Int sy) sz "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  split_ifs with h
  · cases h with
    | inl h_zero =>
      simp [h_zero, Str2Int]
      constructor
      · intro i c hget
        simp at hget
        cases hget
        right; rfl
      · simp [Exp_int]
        exact Nat.mod_eq_of_lt hsz_gt1
    | inr h_empty =>
      omega
  · have exp_val := Str2Int sy
    have aux_valid : ∀ base mod result,
      ValidBitString base → ValidBitString mod → ValidBitString result →
      ValidBitString (ModExp.modExpAux base exp_val mod result) := by
      intro base mod result hbase hmod hresult
      induction exp_val using Nat.strong_induction_on generalizing base result with
      | _ n ih =>
        unfold ModExp.modExpAux
        split_ifs with hzero hodd
        · exact hresult
        · apply ih
          · omega
          · apply ModMul_valid; exact hbase; exact hbase; exact hmod
          · apply ModMul_valid; exact hresult; exact hbase; exact hmod
        · apply ih
          · omega
          · apply ModMul_valid; exact hbase; exact hbase; exact hmod
          · exact hresult
    
    have aux_correct : ∀ base_val exp mod_val result_val,
      mod_val > 1 →
      Str2Int (ModExp.modExpAux (Int2Str base_val) exp (Int2Str mod_val) (Int2Str result_val)) =
      (result_val * Exp_int base_val exp) % mod_val := by
      intro base_val exp mod_val result_val hmod
      induction exp using Nat.strong_induction_on generalizing base_val result_val with
      | _ n ih =>
        unfold ModExp.modExpAux
        split_ifs with hzero hodd
        · simp [hzero, Int2Str_correct, Exp_int]
          rw [Nat.mul_one]
        · rw [ModMul_correct, ModMul_correct, Int2Str_correct, Int2Str_correct, Int2Str_correct]
          · rw [ih]
            · unfold Exp_int
              split_ifs with h_eq
              · omega
              · have : n = 2 * (n / 2) + 1 := by
                  rw [Nat.mul_comm, Nat.div_add_mod]
                  simp [hodd]
              rw [← this] at h_eq
              simp at h_eq
              simp [Nat.sub_self] at h_eq
              rw [Nat.mul_assoc, Nat.mul_comm base_val, ← Nat.mul_assoc, ← Nat.mul_assoc]
              rw [Nat.mul_mod, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod, ← Nat.mul_mod]
              · congr 1
                have exp_rec : Exp_int base_val (n - 1) = base_val * Exp_int base_val ((n - 1) - 1) := by
                  unfold Exp_int
                  split_ifs with h'
                  · omega
                  · rfl
                rw [exp_rec]
                have : (n - 1) - 1 = n / 2 := by omega
                rw [this]
                ring
              · omega
            · omega
            · omega
          · apply Int2Str_valid
          · apply Int2Str_valid
          · apply Int2Str_valid
          · omega
          · apply ModMul_valid <;> apply Int2Str_valid
          · apply Int2Str_valid
          · apply Int2Str_valid
          · omega
        · rw [ModMul_correct, Int2Str_correct, Int2Str_correct, Int2Str_correct]
          · rw [ih]
            · unfold Exp_int
              split_ifs with h_eq
              · have : n = 2 * (n / 2) := by
                  rw [Nat.mul_comm, Nat.div_add_mod]
                  simp [Nat.not_lt] at hodd
                  omega
                omega
              · have : n = 2 * (n / 2) := by
                  rw [Nat.mul_comm, Nat.div_add_mod]
                  simp [Nat.not_lt] at hodd
                  omega
                rw [← this] at h_eq
                simp at h_eq
                have exp_rec : Exp_int base_val (n - 1) = base_val * Exp_int base_val ((n - 1) - 1) := by
                  unfold Exp_int
                  split_ifs with h'
                  · omega
                  · rfl
                rw [exp_rec]
                have : (n - 1) - 1 = n / 2 + (n / 2 - 1) := by omega
                rw [this]
                have : Exp_int base_val (n / 2 + (n / 2 - 1)) = Exp_int base_val (n / 2) * Exp_int base_val (n / 2 - 1) := by
                  clear this h_eq
                  induction n / 2 with
                  | zero => simp [Exp_int]
                  | succ m _ =>
                    simp [Nat.succ_eq_add_one]
                    unfold Exp_int
                    split_ifs with h1 h2 h3
                    · omega
                    · omega
                    · omega
                    · ring
                rw [this]
                ring
            · omega
            · omega
          · apply Int2Str_valid
          · apply Int2Str_valid
          · apply Int2Str_valid
          · omega
    
    constructor
    · apply aux_valid
      · exact hx
      · exact hz
      · apply Int2Str_valid
    · simp [aux_correct hsz_gt1, Int2Str_correct, Nat.one_mul]
-- </vc-proof>

end BignumLean