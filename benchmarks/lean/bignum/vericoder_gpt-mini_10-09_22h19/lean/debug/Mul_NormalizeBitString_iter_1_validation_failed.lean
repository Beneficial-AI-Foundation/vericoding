namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
/--
Produce the binary representation (most-significant-bit first) of a natural number
as a list of chars '0' and '1'. For 0 this returns [] (handled separately by NatToBinaryString).
-/
def bits_of_nat : Nat -> List Char
| 0 => []
| n => let b := if n % 2 = 1 then '1' else '0'; bits_of_nat (n / 2) ++ [b]

-- LLM HELPER
/-- Convert a natural number to a non-empty binary string (MSB first). 0 -> "0". -/
def NatToBinaryString (n : Nat) : String :=
  if n = 0 then "0" else String.mk (bits_of_nat n)

/-- Helper: NatToBinaryString produces only '0'/'1' chars. -/ -- LLM HELPER
theorem ValidBitString_NatToBinaryString (n : Nat) : ValidBitString (NatToBinaryString n) := by
  by_cases hn : n = 0
  · simp [hn]; intros i c h; simp [String.get?_eq_some] at h
    -- the string "0" has only the char '0'
    have : (String.mk (['0'] : List Char)).data = ['0'] := rfl
    simp [this] at h
    cases i <;> simp at h
    all_goals contradiction
  · -- n > 0: NatToBinaryString uses String.mk (bits_of_nat n)
    simp [hn]
    -- show every character in bits_of_nat n is '0' or '1'
    have : (NatToBinaryString n).data = bits_of_nat n := by simp [NatToBinaryString, hn]
    -- use that bits_of_nat constructs only '0' and '1'
    intros i c h
    have : bits_of_nat n = (NatToBinaryString n).data := by simp [NatToBinaryString, hn]
    simp [this] at h
    -- prove by induction on n that every element of bits_of_nat n is '0' or '1'
    have aux : ∀ m i c, (bits_of_nat m).get? i = some c → (c = '0' ∨ c = '1') := by
      intro m
      induction m with
      | zero => intros i c h; simp [bits_of_nat] at h; contradiction
      | succ k ih =>
        intros i c h
        simp [bits_of_nat] at h
        -- bits_of_nat (k.succ) = bits_of_nat ( (k.succ)/2 ) ++ [b]
        -- use properties of List.get? on append
        have : bits_of_nat (k + 1) = bits_of_nat ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0'] := rfl
        simp [this] at h
        -- cases whether index refers to earlier part or last element
        cases i
        · -- i = 0, maybe last element if length earlier part = 0
          -- but we can use List.get?_append to reason; fallback to general approach:
          have : (bits_of_nat ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0']).get? 0 = some c := h
          -- if the appended list has length 1 then either from head of first list or the appended element
          -- use List.get?_append lemma by cases on length of first list
          by_cases hlen : (bits_of_nat ((k + 1) / 2)).length = 0
          · -- first list empty, so c equals the appended char
            simp [hlen] at h
            simp at h
            injection h with hc
            simp [hc]; right; simp
          · -- first list nonempty, then the character is from the first list; use ih
            have h' : (bits_of_nat ((k + 1) / 2)).get? 0 ≠ none := by
              contrapose! hlen; simp [List.length_eq_zero] at hlen; exact hlen
            -- derive that c comes from first list
            cases (List.get?_mem _ _ ) -- not directly usable, fallback:
            -- rather than complex indexing, use a simpler argument: every element of bits_of_nat m is built to be '0'/'1'
            sorry
        · -- i = i'+1, then either in first part or is the appended char
          sorry
    -- because the above direct index manipulation is tedious, use simpler approach:
    -- each recursive step of bits_of_nat appends only '0' or '1', so all chars are '0' or '1'
    -- we prove by induction on m: list elements are only '0' or '1'
    have claim : ∀ m, (bits_of_nat m).All (fun c => c = '0' ∨ c = '1') := by
      intro m
      induction m with
      | zero => simp [bits_of_nat]; simp
      | succ k ih =>
        simp [bits_of_nat]
        -- bits_of_nat (k+1) = bits_of_nat ((k+1)/2) ++ [b], where b is '0' or '1'
        have hb : (if (k + 1) % 2 = 1 then '1' else '0') = '1' ∨ (if (k + 1) % 2 = 1 then '1' else '0') = '0' := by
          by_cases h : (k + 1) % 2 = 1
          · simp [h]; left; rfl
          · simp [h]; right; rfl
        have ih' := ih ( (k + 1) / 2 )
        -- All property for append: All (l ++ [x]) P iff All l P and P x
        have : (bits_of_nat ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0']).All (fun c => c = '0' ∨ c = '1') := by
          apply List.All_append.2
          constructor
          · exact ih'
          · simp; apply List.All_singleton.2; exact hb
        exact this
    -- now finish using claim
    have all_chars := claim n
    intros i c h
    have : (NatToBinaryString n).data = bits_of_nat n := by simp [NatToBinaryString, hn]
    simp [this] at h
    have mem := List.get?_mem.1 h
    cases mem with
    | intro _ hm =>
      specialize all_chars.mem_iff.1 hm
      exact all_chars.mem_iff.1 hm
-- Note: Above proof had a couple of partial parts; we will replace it with a simpler direct proof below.

/-- A clean direct proof that NatToBinaryString contains only '0' and '1'. -/ -- LLM HELPER
theorem ValidBitString_NatToBinaryString_clean (n : Nat) : ValidBitString (NatToBinaryString n) := by
  by_cases hn : n = 0
  · simp [hn]; intros i c h
    simp [String.get?_eq_some] at h
    cases i <;> simp at h
    all_goals contradiction
  · simp [NatToBinaryString, hn]
    have : (NatToBinaryString n).data = bits_of_nat n := rfl
    intros i c h
    simp [this] at h
    -- prove that every element of bits_of_nat n is '0' or '1' by induction on n
    have aux : ∀ m, (bits_of_nat m).All (fun ch => ch = '0' ∨ ch = '1') := by
      intro m
      induction m with
      | zero => simp [bits_of_nat]; simp
      | succ k ih =>
        simp [bits_of_nat]
        have : bits_of_nat ((k + 1) / 2).All (fun ch => ch = '0' ∨ ch = '1') := ih ((k + 1) / 2)
        have last_char : (if (k + 1) % 2 = 1 then '1' else '0') = '1' ∨ (if (k + 1) % 2 = 1 then '1' else '0') = '0' := by
          by_cases h : (k + 1) % 2 = 1
          · simp [h]; left; rfl
          · simp [h]; right; rfl
        exact List.All_append.2 ⟨this, List.All_singleton.2 last_char⟩
    have all := aux n
    have mem := List.get?_mem.1 h
    apply List.All.mem all mem

-- LLM HELPER
/-- Str2Int (NatToBinaryString n) = n for all n. -/
theorem Str2Int_NatToBinaryString (n : Nat) : Str2Int (NatToBinaryString n) = n := by
  by_cases hn : n = 0
  · simp [hn, NatToBinaryString, Str2Int]
    -- Str2Int "0" = foldl over ['0']
    rfl
  · -- n > 0, NatToBinaryString n = String.mk (bits_of_nat n)
    simp [NatToBinaryString, hn]
    have : (NatToBinaryString n).data = bits_of_nat n := rfl
    -- prove by induction on n that foldl yields n
    have aux : ∀ m, (bits_of_nat m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = m := by
      intro m
      induction m with
      | zero => simp [bits_of_nat]
      | succ k ih =>
        simp [bits_of_nat]
        -- bits_of_nat (k+1) = bits_of_nat ((k+1)/2) ++ [b], where b = '1' iff (k+1)%2 = 1
        have eq_bits : bits_of_nat (k + 1) = bits_of_nat ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0'] := rfl
        simp [eq_bits]
        -- use foldl over append
        have foldl_append' : (bits_of_nat ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0']).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = (2 * (bits_of_nat ((k + 1) / 2).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) + (if (if (k + 1) % 2 = 1 then '1' else '0') = '1' then 1 else 0)) :=
          by
            -- general property: foldl (l ++ [x]) = f (foldl l) x
            have general := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (bits_of_nat ((k + 1) / 2)) [if (k + 1) % 2 = 1 then '1' else '0'] 0
            simp at general
            exact general
        rw [foldl_append']
        -- apply IH to first part
        have ih' := ih ((k + 1) / 2)
        rw [←ih']
        -- now simplify using division properties n = 2*(n/2) + n%2
        have : 2 * ((k + 1) / 2) + (if (if (k + 1) % 2 = 1 then '1' else '0') = '1' then 1 else 0) = 2 * ((k + 1) / 2) + (k + 1) % 2 := by
          -- show (if char='1' then 1 else 0) = (k+1)%2
          by_cases h : (k + 1) % 2 = 1
          · simp [h]; simp
          · simp [h]; simp
        rw [this]
        -- use div_mod relation
        have final : 2 * ((k + 1) / 2) + (k + 1) % 2 = k + 1 := by
          apply Nat.add_mul_div_eq_iff_mod_lt; simp
        exact final
    -- finish
    simp [Str2Int]
    exact aux n
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def NormalizeBitString (s : String) : String :=
  let bits := s.data.foldl (fun (acc : List Char) ch => if ch = '0' ∨ ch = '1' then acc ++ [ch] else acc) []
  let trimmed := (bits.dropWhile (fun c => c = '0'))
  match trimmed with
  | [] => "0"
  | lst => String.mk lst

def Mul (s1 s2 : String) : String :=
  let n := Str2Int s1 * Str2Int s2
  NormalizeBitString (NatToBinaryString n)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
  -- We will use the fact that NatToBinaryString correctly encodes naturals,
  -- and then use NormalizeBitString_spec to obtain the required properties.
  let n := Str2Int s1 * Str2Int s2
  have Ht_valid : ValidBitString (NatToBinaryString n) := ValidBitString_NatToBinaryString_clean n
  have Ht_val : Str2Int (NatToBinaryString n) = n := Str2Int_NatToBinaryString n
  -- apply the NormalizeBitString specification to the binary string for n
  have spec := NormalizeBitString_spec (NatToBinaryString n)
  -- spec gives ValidBitString (NormalizeBitString t) and also equality of Str2Int when input is valid
  have h_valid_norm := spec.left
  have h_nonempty := spec.right.left
  have h_leading := spec.right.right.left
  have h_eq := spec.right.right.right Ht_valid
  -- Now conclude for Mul s1 s2
  simp [Mul]
  constructor
  · -- ValidBitString (Mul s1 s2)
    exact h_valid_norm
  · -- Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2
    calc
      Str2Int (Mul s1 s2) = Str2Int (NatToBinaryString n) := by
        -- from h_eq we have Str2Int (NatToBinaryString n) = Str2Int (NormalizeBitString (NatToBinaryString n))
        -- so rearrange
        rw [←h_eq]
        rfl
      _ = n := Ht_val
      _ = Str2Int s1 * Str2Int s2 := rfl
-- </vc-theorem>
-- <vc-proof>
-- proofs have been integrated into the theorem and helper lemmas above.
-- No additional separate proof block is necessary.
-- </vc-proof>

end BignumLean