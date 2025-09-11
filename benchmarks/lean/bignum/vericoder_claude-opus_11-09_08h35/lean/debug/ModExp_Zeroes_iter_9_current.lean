namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def Nat2BitString (n : Nat) (len : Nat) : String :=
  let rec toBits (n : Nat) (acc : List Char) (remaining : Nat) : List Char :=
    if remaining = 0 then acc
    else toBits (n / 2) ((if n % 2 = 0 then '0' else '1') :: acc) (remaining - 1)
  String.mk (toBits n [] len)

-- LLM HELPER
lemma Nat2BitString_length (n len : Nat) : (Nat2BitString n len).length = len := by
  simp [Nat2BitString, String.length]
  generalize hlist : Nat2BitString.toBits n [] len = list
  have : list.length = len := by
    rw [← hlist]
    clear hlist
    induction len generalizing n with
    | zero => simp [Nat2BitString.toBits]
    | succ l ih =>
      simp [Nat2BitString.toBits]
      exact ih (n / 2)
  exact this

-- LLM HELPER
lemma Nat2BitString_valid (n len : Nat) : ValidBitString (Nat2BitString n len) := by
  intro i c h
  simp [Nat2BitString, ValidBitString, String.get?, String.data] at h ⊢
  generalize hlist : Nat2BitString.toBits n [] len = list at h
  have : ∀ c ∈ list, c = '0' ∨ c = '1' := by
    rw [← hlist]
    clear hlist h
    induction len generalizing n with
    | zero => 
      simp [Nat2BitString.toBits]
    | succ l ih =>
      simp [Nat2BitString.toBits]
      intro c hc
      apply ih
      exact hc
  exact this c (List.mem_of_get? h)

-- LLM HELPER  
lemma Nat2BitString_bound (n len : Nat) (h : n < 2^len) : 
  Str2Int (Nat2BitString n len) = n := by
  simp [Nat2BitString, Str2Int, String.data]
  generalize hlist : Nat2BitString.toBits n [] len = list
  have : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 list = n := by
    rw [← hlist]
    clear hlist
    induction len generalizing n with
    | zero =>
      simp [Nat2BitString.toBits]
      have : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (by simp at h; exact h))
      exact this
    | succ l ih =>
      simp [Nat2BitString.toBits]
      have bound' : n / 2 < 2^l := by
        have : n < 2 * 2^l := by simp [Nat.pow_succ] at h; exact h
        exact Nat.div_lt_iff_lt_mul (by norm_num) |>.mpr this
      rw [ih (n / 2) bound']
      split_ifs with hmod <;> simp
      · have : n = 2 * (n / 2) := by
          rw [Nat.mul_comm]
          exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)).symm
        rw [this]
      · have mod_val : n % 2 = 1 := by
          have : n % 2 < 2 := Nat.mod_lt n (by norm_num)
          have : n % 2 ≠ 0 := hmod
          interval_cases n % 2
        have : n = 2 * (n / 2) + 1 := by
          rw [← mod_val]
          exact (Nat.div_add_mod n 2).symm
        rw [this]
        ring
  exact this
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sz.length = 0 || Str2Int sz ≤ 1 then
    Zeros sx.length
  else
    let x := Str2Int sx
    let y := Str2Int sy
    let z := Str2Int sz
    let result := Exp_int x y % z
    Nat2BitString result sx.length
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
simp [ModExp]
  split_ifs with h
  · -- Case where sz.length = 0 or Str2Int sz ≤ 1
    cases h with
    | inl h1 => 
      have : Str2Int sz = 0 := by
        cases sz with
        | mk data =>
          simp [String.length] at h1
          simp [Str2Int]
          cases data
          · rfl
          · contradiction
      linarith
    | inr h2 => linarith
  · -- Main case
    push_neg at h
    constructor
    · exact Nat2BitString_valid _ _
    · have mod_bound : Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz < 2^sx.length := by
        have h1 : Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz < Str2Int sz := 
          Nat.mod_lt _ hsz_gt1
        have h2 : Str2Int sz ≤ 2^sz.length := by
          clear h1
          simp [Str2Int]
          generalize hdata : sz.data = data
          have : data.length = sz.length := by simp [← hdata, String.length]
          rw [← this]
          clear this hdata
          induction data with
          | nil => simp
          | cons c cs ih =>
            simp [List.foldl]
            calc List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
                    (if c = '1' then 1 else 0) cs
              ≤ List.foldl (fun acc ch => 2 * acc + 1) 1 cs := by
                apply List.foldl_monotone_simple
                · intro; linarith
                · split_ifs; simp; simp
              _ ≤ 2^(cs.length + 1) - 1 := by
                clear ih
                induction cs generalizing (1 : Nat) with
                | nil => simp
                | cons _ cs' ih' =>
                  simp [List.foldl, Nat.pow_succ]
                  calc List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 
                          (2 * 1 + (if _ = '1' then 1 else 0)) cs'
                    ≤ List.foldl (fun acc ch => 2 * acc + 1) 3 cs' := by
                      apply List.foldl_monotone_simple
                      · intro; linarith
                      · split_ifs <;> simp
                    _ ≤ 3 * 2^cs'.length := by
                      clear ih'
                      induction cs' generalizing (3 : Nat) with
                      | nil => simp
                      | cons _ cs'' ih'' =>
                        simp [List.foldl]
                        calc List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
                                (2 * 3 + (if _ = '1' then 1 else 0)) cs''
                          ≤ List.foldl (fun acc ch => 2 * acc + 1) 7 cs'' := by
                            apply List.foldl_monotone_simple
                            · intro; linarith
                            · split_ifs <;> simp
                          _ ≤ 7 * 2^cs''.length := ih'' 7
                          _ ≤ 2 * 2^(cs''.length + 1) + 3 * 2^cs''.length := by
                            simp [Nat.pow_succ]; linarith
                    _ ≤ 2 * 2^cs'.length + 2^cs'.length := by linarith
                    _ = 3 * 2^cs'.length := by ring
                    _ ≤ 2 * 2^(cs'.length + 1) - 1 := by 
                      simp [Nat.pow_succ]
                      have : 1 ≤ 2^cs'.length := Nat.one_le_pow_iff.mpr (by norm_num)
                      linarith
              _ < 2^(cs.length + 1) := Nat.sub_lt (by apply Nat.zero_lt_pow_iff; norm_num) (by norm_num)
        have h3 : Str2Int sz ≤ 2^sx.length := by
          by_cases hcmp : sz.length ≤ sx.length
          · calc Str2Int sz 
              ≤ 2^sz.length := h2
              _ ≤ 2^sx.length := Nat.pow_le_pow_right (by norm_num) hcmp
          · push_neg at hcmp
            have sx_pos : 0 < sx.length := by
              by_contra h_neg
              push_neg at h_neg
              have : sx.length = 0 := Nat.eq_zero_of_le_zero h_neg
              have : sz.length = 0 := by linarith
              simp [this] at h
            have : 1 < 2^sx.length := by
              calc 1 < 2 := by norm_num
                _ ≤ 2^sx.length := Nat.le_self_pow sx_pos (by norm_num)
            calc Str2Int sz
              ≤ 2^sz.length := h2
              _ ≤ 2^sz.length := Nat.le_refl _
              _ ≤ 2^sx.length := by
                clear h1 h2
                have : Str2Int sx < 2^sx.length := by
                  simp [Str2Int]
                  generalize hdata : sx.data = data
                  have : data.length = sx.length := by simp [← hdata, String.length]
                  rw [← this]
                  clear this hdata
                  induction data with
                  | nil => simp
                  | cons c cs ih =>
                    simp [List.foldl]
                    calc List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
                            (if c = '1' then 1 else 0) cs
                      ≤ List.foldl (fun acc ch => 2 * acc + 1) 1 cs := by
                        apply List.foldl_monotone_simple
                        · intro; linarith  
                        · split_ifs; simp; simp
                      _ < 2^(cs.length + 1) := by
                        clear ih
                        induction cs generalizing (1 : Nat) with
                        | nil => simp; norm_num
                        | cons _ cs' ih' =>
                          simp [List.foldl, Nat.pow_succ]
                          calc List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
                                  (2 * 1 + (if _ = '1' then 1 else 0)) cs'
                            ≤ List.foldl (fun acc ch => 2 * acc + 1) 3 cs' := by
                              apply List.foldl_monotone_simple
                              · intro; linarith
                              · split_ifs <;> simp
                            _ < 2 * 2^cs'.length := by
                              have : List.foldl (fun acc ch => 2 * acc + 1) 3 cs' < 2^(cs'.length + 1) := ih' 3
                              simp [Nat.pow_succ] at this
                              linarith
                linarith
        linarith
      exact Nat2BitString_bound _ _ mod_bound
-- </vc-proof>

end BignumLean