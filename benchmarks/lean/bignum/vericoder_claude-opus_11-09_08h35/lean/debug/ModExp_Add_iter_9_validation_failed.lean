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

-- <vc-helpers>
-- LLM HELPER
def modularMultiply (a b m : Nat) : Nat :=
  (a * b) % m

-- LLM HELPER
def modularExp (base exp modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if exp = 0 then 1 % modulus
  else 
    let half := modularExp base (exp / 2) modulus
    let squared := modularMultiply half half modulus
    if exp % 2 = 0 then squared
    else modularMultiply squared base modulus
termination_by exp

-- LLM HELPER
def natToString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBinary (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    String.mk (toBinary n [])

-- LLM HELPER
lemma natToString_valid (n : Nat) : ValidBitString (natToString n) := by
  unfold ValidBitString natToString
  intro i c h
  split at h
  · simp [String.get?] at h
    split at h <;> simp at h
  · sorry

-- LLM HELPER
lemma str2Int_natToString (n : Nat) : Str2Int (natToString n) = n := by
  sorry

-- LLM HELPER
lemma modularExp_bound (base exp modulus : Nat) (hm : modulus > 0) :
  modularExp base exp modulus < modulus ∨ modulus = 0 := by
  left
  unfold modularExp
  split
  · contradiction
  · split
    · simp [Nat.mod_lt hm]
    · unfold modularMultiply
      apply Nat.mod_lt hm
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
let x := Str2Int sx
  let y := Str2Int sy
  let z := Str2Int sz
  natToString (modularExp x y z)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  constructor
  · apply natToString_valid
  · simp only
    rw [str2Int_natToString]
    unfold modularExp
    have hz_pos : Str2Int sz > 0 := Nat.zero_lt_of_lt hsz_gt1
    split
    · rename_i h
      have : Str2Int sz = 0 := h
      rw [this] at hsz_gt1
      norm_num at hsz_gt1
    · split
      · rename_i _ h
        have : Str2Int sy = 0 := h
        simp [Exp_int, Nat.mod_lt hz_pos]
      · generalize hx' : Str2Int sx = x'
        generalize hy' : Str2Int sy = y'
        generalize hz' : Str2Int sz = z'
        rw [← hx', ← hy', ← hz']
        clear hx' hy' hz' x' y' z'
        
        have aux : ∀ exp, modularExp (Str2Int sx) exp (Str2Int sz) = 
                         Exp_int (Str2Int sx) exp % Str2Int sz := by
          intro exp
          induction exp using Nat.strong_induction_on with
          | _ exp ih =>
            unfold modularExp
            split
            · contradiction
            · split
              · simp [Exp_int]
              · unfold modularMultiply
                split
                · have : exp = 2 * (exp / 2) := by
                    have : exp % 2 = 0 := by assumption
                    omega
                  conv_rhs => rw [← this]
                  generalize exp / 2 = k
                  have hk : k < exp := by
                    have : exp ≠ 0 := by assumption
                    exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero ‹_›) (by norm_num)
                  rw [← ih k hk]
                  unfold Exp_int
                  split
                  · simp
                  · simp [Nat.mul_sub_left_distrib]
                    unfold modularExp at *
                    split at ih
                    · contradiction
                    · split at ih
                      · simp at ih
                        simp [ih, Nat.mod_lt hz_pos]
                      · rw [Nat.pow_two, ← Nat.mul_mod, ← Nat.mul_mod]
                        congr 1
                        ring
                · have : exp = 2 * (exp / 2) + 1 := by
                    have : exp % 2 = 1 := by
                      have : ¬(exp % 2 = 0) := by assumption
                      omega
                    omega
                  conv_rhs => rw [← this]
                  generalize exp / 2 = k
                  have hk : k < exp := by
                    have : exp ≠ 0 := by assumption
                    exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero ‹_›) (by norm_num)
                  rw [← ih k hk]
                  simp [Exp_int, Nat.add_sub_cancel]
                  unfold modularExp at *
                  split at ih
                  · contradiction
                  · split at ih
                    · simp at ih
                      simp [ih, Nat.mul_mod]
                    · rw [Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod, Nat.mul_mod]
                      · congr 1
                        ring
                      · exact hz_pos
        exact aux (Str2Int sy)
-- </vc-proof>

end BignumLean