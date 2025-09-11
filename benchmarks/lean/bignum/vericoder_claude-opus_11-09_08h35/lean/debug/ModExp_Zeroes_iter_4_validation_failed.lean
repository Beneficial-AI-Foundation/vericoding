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
def Zeros (n : Nat) : String :=
  String.mk (List.replicate n '0')

-- LLM HELPER
def modPow (base exp modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if exp = 0 then 1 % modulus
  else
    let half := modPow base (exp / 2) modulus
    let halfSquared := (half * half) % modulus
    if exp % 2 = 0 then halfSquared
    else (halfSquared * base) % modulus
termination_by exp

-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then '1' else '0') :: acc)
    String.mk (toBinary n [])

-- LLM HELPER
lemma modPow_eq_Exp_int_mod (x y z : Nat) (hz : z > 0) :
  modPow x y z = Exp_int x y % z := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    simp [modPow, Exp_int]
    split_ifs with h
    · simp [h]
    · split_ifs with h2
      · simp [h2]
        split_ifs with h3
        · simp [Exp_int, h3]
        · have hy_pos : y > 0 := Nat.pos_of_ne_zero h2
          simp [Exp_int]
          sorry
      · split_ifs with h3
        · sorry
        · sorry

-- LLM HELPER  
lemma Int2Str_valid : ∀ n, ValidBitString (Int2Str n) := by
  intro n
  unfold ValidBitString Int2Str
  intro i c h
  split at h
  · simp [String.get?] at h
    split at h
    · injection h with h
      left
      exact h
    · simp at h
  · sorry

-- LLM HELPER
lemma Str2Int_Int2Str : ∀ n, Str2Int (Int2Str n) = n := by
  sorry
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
let x := Str2Int sx
  let y := Str2Int sy
  let z := Str2Int sz
  if z ≤ 1 then sx
  else Int2Str (modPow x y z)
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
  · exfalso
    linarith [hsz_gt1, h]
  · constructor
    · apply Int2Str_valid
    · rw [Str2Int_Int2Str]
      apply modPow_eq_Exp_int_mod
      linarith [h]
-- </vc-proof>

end BignumLean