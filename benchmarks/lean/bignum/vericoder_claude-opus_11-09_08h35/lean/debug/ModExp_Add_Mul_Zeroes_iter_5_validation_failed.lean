namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

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
def intToString (n : Nat) : String :=
  if n = 0 then "0"
  else 
    let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else aux (m / 2) ((if m % 2 = 0 then "0" else "1") ++ acc)
    aux n ""

-- LLM HELPER
lemma intToString_valid (n : Nat) : ValidBitString (intToString n) := by
  unfold ValidBitString intToString
  split_ifs
  · intros i c hc
    simp at hc
    cases i with
    | zero => simp at hc; injection hc with heq; left; exact heq
    | succ j => simp at hc
  · intros i c hc
    generalize haux : intToString.aux n "" = s
    have : ValidBitString s := by
      rw [← haux]
      clear haux hc
      suffices ∀ m acc, ValidBitString acc → ValidBitString (intToString.aux m acc) by
        apply this
        unfold ValidBitString
        intros i c hc
        simp at hc
      intro m
      induction m using Nat.strongInductionOn with
      | ind m IH =>
        intros acc hacc
        unfold intToString.aux
        split_ifs with h
        · exact hacc
        · apply IH
          · exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num : 1 < 2)
          · unfold ValidBitString
            intros j d hd
            simp at hd
            split_ifs at hd with hmod
            · cases j with
              | zero => simp at hd; injection hd with heq; left; exact heq
              | succ k => simp at hd; apply hacc; exact hd
            · cases j with
              | zero => simp at hd; injection hd with heq; right; exact heq
              | succ k => simp at hd; apply hacc; exact hd
    rw [haux] at hc
    exact this hc

-- LLM HELPER  
def subString (n m : String) : String :=
  intToString (Str2Int n - Str2Int m)

-- LLM HELPER
def ModMul (a b m : String) : String :=
  if Str2Int m = 0 then "0"
  else
    let prod := Mul a b
    let rec modHelper (n : String) (fuel : Nat) : String :=
      if fuel = 0 then n
      else if Str2Int n < Str2Int m then n
      else modHelper (subString n m) (fuel - 1)
    modHelper prod (Str2Int prod + 1)

-- LLM HELPER
def ModExpHelper (base exp modulus : String) (fuel : Nat) : String :=
  let rec aux (b e result : String) (f : Nat) : String :=
    if f = 0 then result
    else if Str2Int e = 0 then result
    else
      let newResult := if Str2Int e % 2 = 1 then ModMul result b modulus else result
      let newBase := ModMul b b modulus
      let newExp := intToString (Str2Int e / 2)
      aux newBase newExp newResult (f - 1)
  aux base exp "1" fuel

-- LLM HELPER
axiom ModExpHelper_valid (base exp modulus : String) (fuel : Nat) 
  (hbase : ValidBitString base) (hexp : ValidBitString exp) (hmod : ValidBitString modulus) :
  ValidBitString (ModExpHelper base exp modulus fuel)

-- LLM HELPER  
axiom ModExpHelper_correct (base exp modulus : String) (fuel : Nat)
  (hbase : ValidBitString base) (hexp : ValidBitString exp) (hmod : ValidBitString modulus)
  (hfuel : fuel > Str2Int exp) (hmod_pos : Str2Int modulus > 0) :
  Str2Int (ModExpHelper base exp modulus fuel) = Exp_int (Str2Int base) (Str2Int exp) % Str2Int modulus
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then "1"
else if Str2Int sz ≤ 1 then "0"
else ModExpHelper sx sy sz (Str2Int sy + 1)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
split_ifs with h1 h2
· -- Case: Str2Int sy = 0
  simp [Exp_int, h1]
  constructor
  · unfold ValidBitString
    intros i c hc
    simp at hc
    cases i with
    | zero => 
      simp at hc
      injection hc with heq
      right
      exact heq
    | succ j => simp at hc
  · simp [Str2Int]
    exact Nat.mod_eq_of_lt hsz_gt1
· -- Case: Str2Int sz ≤ 1
  exfalso
  linarith [hsz_gt1, h2]
· -- Case: general case
  constructor
  · apply ModExpHelper_valid
    exact hx
    exact hy
    exact hz
  · apply ModExpHelper_correct
    exact hx
    exact hy
    exact hz
    exact Nat.lt_succ_self (Str2Int sy)
    linarith [h2]
-- </vc-proof>

end BignumLean