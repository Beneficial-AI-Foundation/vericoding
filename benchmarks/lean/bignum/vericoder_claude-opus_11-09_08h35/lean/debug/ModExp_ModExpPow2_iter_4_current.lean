namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

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
def getBit (s : String) (i : Nat) : Bool :=
  if h : i < s.length then
    s.get ⟨i, h⟩ = '1'
  else false

-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc else
        aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    aux n ""

-- LLM HELPER
def ModExpAux (sx : String) (sy : String) (sz : String) (i : Nat) (acc : String) : String :=
  if h : i < sy.length then
    let bit_set := getBit sy i
    let pow2_exp := String.mk (List.replicate i '0' ++ ['1'])
    let partial := ModExpPow2 sx pow2_exp i sz
    let new_acc := if bit_set then
      Int2Str ((Str2Int acc * Str2Int partial) % Str2Int sz)
    else acc
    ModExpAux sx sy sz (i + 1) new_acc
  else acc
termination_by sy.length - i

-- LLM HELPER
lemma ValidBitString_Int2Str (n : Nat) : ValidBitString (Int2Str n) := by
  intro i c hc
  unfold Int2Str at hc
  split at hc
  · simp at hc
    cases hc with
    | inl h => exact Or.inl h
    | inr h => cases h
  · simp at hc
    generalize haux : (let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc else
        aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
      aux n "") = result at hc
    have : ∀ m acc i c, (let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc else
        aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
      aux m acc).get? i = some c → c = '0' ∨ c = '1' := by
      intro m acc
      induction m using Nat.strong_induction_on generalizing acc with
      | _ m ih =>
        intro i c hget
        simp at hget
        split at hget
        · rw [hget]
          simp
          split <;> simp
        · have := ih (m / 2) (by omega) _ i c
          apply this
          exact hget
    exact this n "" i c (haux ▸ hc)
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sy.length = 0 then "1" else ModExpAux sx sy sz 0 "1"
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
· omega
· constructor
  · apply ValidBitString_Int2Str
  · have : Str2Int "1" = 1 := by rfl
    have hz_pos : Str2Int sz > 0 := by omega
    have : 1 % Str2Int sz = 1 := Nat.mod_eq_of_lt hsz_gt1
    simp [ModExpAux, getBit, Int2Str, Str2Int, Exp_int]
    generalize hresult : ModExpAux sx sy sz 0 "1" = result
    have : ValidBitString result ∧ Str2Int result = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
      clear hresult result
      suffices ∀ i acc, i ≤ sy.length → ValidBitString acc → 
        let result := ModExpAux sx sy sz i acc
        ValidBitString result ∧ 
        Str2Int result = (Str2Int acc * Exp_int (Str2Int sx) (Str2Int (String.mk (sy.data.drop i)))) % Str2Int sz by
        specialize this 0 "1" (by omega) (by intro i c hc; simp at hc; cases hc with | inl h => exact Or.inr h | inr h => cases h)
        simp at this
        convert this using 2
        simp [Str2Int, Exp_int]
        rfl
      intro i acc hi hacc
      induction' hi' : sy.length - i with k ih generalizing i acc
      · simp [ModExpAux]
        split_ifs with h_cond
        · omega
        · constructor
          · exact hacc
          · have : sy.data.drop i = [] := by
              have : i = sy.length := by omega
              simp [this]
            simp [this, Str2Int, Exp_int]
            ring_nf
      · simp [ModExpAux]
        split_ifs with h_cond
        · have hi_lt : i < sy.length := by omega
          simp at ih
          specialize ih (i + 1) _ (by omega) (by omega)
          split_ifs <;> simp [getBit, Int2Str, ValidBitString_Int2Str]
          apply ih
          apply ValidBitString_Int2Str
        · omega
    exact this
-- </vc-proof>

end BignumLean