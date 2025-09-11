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

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def MultiplyMod (sx sz acc : String) : String :=
  let rec loop (n : Nat) (result : String) : String :=
    if n = 0 then result
    else
      let doubled := Add result result
      if Str2Int doubled < Str2Int sz then
        loop (n - 1) doubled
      else
        loop (n - 1) (Add doubled (Zeros sz.length))
  loop (Str2Int sx) acc

-- LLM HELPER  
def ModExpHelper (sx sy sz : String) (fuel : Nat) : String :=
  if fuel = 0 then Zeros sz.length
  else if sy = Zeros sy.length then Zeros sz.length
  else if Str2Int sy = 1 then 
    if Str2Int sx < Str2Int sz then sx else Zeros sz.length
  else
    let half_exp := ModExpHelper (MultiplyMod sx sz sx) (Zeros (sy.length - 1)) sz (fuel - 1)
    if Str2Int sy % 2 = 0 then half_exp
    else MultiplyMod sx sz half_exp
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
ModExpHelper sx sy sz (Str2Int sy + 1)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  have h_valid : ValidBitString (ModExpHelper sx sy sz (Str2Int sy + 1)) := by
    unfold ModExpHelper
    split_ifs
    · exact (Zeros_spec sz.length).2.1
    · exact (Zeros_spec sz.length).2.1
    · split_ifs
      · exact hx
      · exact (Zeros_spec sz.length).2.1
    · have h_multi : ValidBitString (MultiplyMod sx sz sx) := by
        unfold MultiplyMod MultiplyMod.loop
        split_ifs
        · exact (Zeros_spec sz.length).2.1
        · have : ValidBitString (Add sx sx) := (Add_spec sx sx hx hx).1
          exact this
        · have h1 : ValidBitString (Add sx sx) := (Add_spec sx sx hx hx).1
          have h2 : ValidBitString (Zeros sz.length) := (Zeros_spec sz.length).2.1
          exact (Add_spec _ _ h1 h2).1
      split_ifs
      · exact (Zeros_spec (sy.length - 1)).2.1
      · unfold MultiplyMod MultiplyMod.loop
        split_ifs
        · exact (Zeros_spec sz.length).2.1
        · exact hx
        · exact (Add_spec _ _ hx (Zeros_spec sz.length).2.1).1
  constructor
  · exact h_valid
  · unfold ModExpHelper
    split_ifs <;> simp [Str2Int, Exp_int]
    · have : Str2Int (Zeros sz.length) = 0 := (Zeros_spec sz.length).2.2.1
      rw [this]
      simp [Exp_int]
      exact Nat.zero_mod _
    · have : Str2Int (Zeros sz.length) = 0 := (Zeros_spec sz.length).2.2.1
      rw [this]
      simp [Exp_int]
      exact Nat.zero_mod _
    · split_ifs
      · simp [Exp_int]
        exact Nat.mod_eq_of_lt (by linarith)
      · have : Str2Int (Zeros sz.length) = 0 := (Zeros_spec sz.length).2.2.1
        rw [this]
        simp [Exp_int]
        exact Nat.zero_mod _
    · simp [Exp_int]
-- </vc-proof>

end BignumLean