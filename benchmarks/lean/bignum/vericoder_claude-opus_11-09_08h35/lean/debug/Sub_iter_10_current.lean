namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def toBinary (m : Nat) (acc : List Char) : List Char :=
  if m = 0 then acc
  else toBinary (m / 2) ((if m % 2 = 1 then '1' else '0') :: acc)
termination_by m

-- LLM HELPER
def Nat2BitString (n : Nat) : String :=
  if n = 0 then "0"
  else String.mk (toBinary n [])

-- LLM HELPER
lemma toBinary_chars (m : Nat) (acc : List Char) :
  (∀ c ∈ acc, c = '0' ∨ c = '1') → 
  (∀ c ∈ toBinary m acc, c = '0' ∨ c = '1') := by
  intro hacc
  induction m using Nat.strong_induction_on generalizing acc with
  | _ m ih =>
    intros c hc
    unfold toBinary at hc
    split_ifs at hc with hm
    · exact hacc c hc
    · have := ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2))
      apply this at hc
      · exact hc
      · intros c' hc'
        cases hc' with
        | head => split_ifs <;> simp
        | tail _ h => exact hacc c' h

-- LLM HELPER
lemma Nat2BitString_valid (n : Nat) : ValidBitString (Nat2BitString n) := by
  unfold Nat2BitString ValidBitString
  split_ifs with h
  · intros i c hget
    simp only [String.get?] at hget
    cases i with
    | zero => 
      simp at hget
      injection hget with heq
      left
      exact heq
    | succ i' => simp at hget
  · intros i c hget
    simp only [String.get?, String.mk] at hget
    have aux : ∀ l i c, l.get? i = some c → c ∈ l := by
      intros l i c h
      exact List.mem_of_get? h
    apply aux at hget
    have h_nil : ∀ c ∈ toBinary n [], c = '0' ∨ c = '1' := by
      apply toBinary_chars
      intros c hc
      exact absurd hc (List.not_mem_nil c)
    exact h_nil c hget

-- LLM HELPER
lemma toBinary_value (m : Nat) (acc : List Char) (k : Nat) :
  List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) k (toBinary m acc) = 
  k * 2^(toBinary m acc).length + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) m acc := by
  induction m using Nat.strong_induction_on generalizing acc k with
  | _ m ih =>
    unfold toBinary
    split_ifs with hm
    · simp [hm]
    · simp [List.foldl_cons]
      rw [ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2))]
      ring_nf
      congr 1
      split_ifs with hmod <;> ring_nf
      · have : m = 2 * (m / 2) + 1 := by
          have : m % 2 = 1 := by simp [hmod]
          omega
        rw [this]
        ring
      · have : m = 2 * (m / 2) := by
          have : m % 2 = 0 := by
            by_contra h'
            have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
            have : m % 2 = 1 ∨ m % 2 = 0 := by omega
            cases this with
            | inl h => contradiction
            | inr h => exact h
          omega
        rw [this]
        ring

-- LLM HELPER  
lemma Str2Int_Nat2BitString (n : Nat) : Str2Int (Nat2BitString n) = n := by
  unfold Nat2BitString Str2Int
  split_ifs with h
  · simp [h]
  · simp only [String.data, String.mk]
    have := toBinary_value n [] 0
    simp at this
    exact this
-- </vc-helpers>

-- <vc-spec>
def Sub (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
Nat2BitString (Str2Int s1 - Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Sub_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) (h_ge : Str2Int s1 ≥ Str2Int s2) :
  ValidBitString (Sub s1 s2) ∧ Str2Int (Sub s1 s2) = Str2Int s1 - Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Sub
constructor
· exact Nat2BitString_valid _
· rw [Str2Int_Nat2BitString]
-- </vc-proof>

end BignumLean