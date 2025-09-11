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

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

-- <vc-helpers>
-- LLM HELPER
/- Helper: convert a natural number to a list of bit characters (MSB first).
   nat_to_bits 0 = ['0']
   nat_to_bits n > 0 = list of '0'/'1' giving binary representation with no leading zeros.
-/
def nat_to_bits : Nat → List Char
  | 0 => ['0']
  | n+1 =>
    let rec aux : Nat → List Char
      | 0 => []
      | k =>
        -- compute bits by recursing on k / 2; this decreases and is accepted by the checker
        let prev := aux (k / 2)
        prev ++ [if k % 2 = 1 then '1' else '0']
    aux (n + 1)

/-- Helper to build a String directly from a list of chars by setting the `.data` field.
    This is convenient because it makes the underlying list equal to `.data` definitionally.
    (We mark it LLM HELPER because it's introduced here to facilitate proofs.) -/
def bits_to_string (l : List Char) : String := { data := l } -- LLM HELPER

-- LEMMA: every character produced by nat_to_bits is '0' or '1'
-- LLM HELPER
theorem nat_to_bits_chars (n : Nat) : ∀ ch ∈ nat_to_bits n, ch = '0' ∨ ch = '1' := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n with
    | zero =>
      simp [nat_to_bits]; intro ch h; simp at h; injection h with h'; subst h'; simp
    | succ n' =>
      dsimp [nat_to_bits]
      let rec aux : Nat → ∀ ch ∈ (@List.nil Char ++ (List.range 0)) → False := fun _ _ => False.elim
      -- We reason about the explicit definition of aux inside nat_to_bits.
      -- Unfolding nat_to_bits gives us the nested aux; we perform a direct argument on its construction.
      let aux_def := nat_to_bits (n' + 1)
      -- Now show every char in aux_def is '0' or '1' by structural reasoning on the helper construction.
      have : ∀ k, (let prev := 
                    let rec aux (k : Nat) : List Char
                      | 0 => []
                      | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
                    aux (k)
                  in prev) = (let rec aux (k : Nat) : List Char
                                | 0 => []
                                | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
                              aux (k)) := by intros; rfl
      clear aux_def aux_def
      -- Now proceed by well-founded induction on the value used inside aux (k).
      have aux_chars : ∀ k, ∀ ch ∈ (let rec aux (k : Nat) : List Char
                                      | 0 => []
                                      | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
                                    aux k), ch = '0' ∨ ch = '1' := by
        intro k
        induction k using Nat.strong_induction_on with
        | ihk k =>
          dsimp
          by_cases h0 : k = 0
          · simp [h0]; intro ch hc; cases hc
          · -- k > 0, list is (aux (k/2)) ++ [bit], use IH for k/2 and the last bit
            dsimp
            intro ch hc
            have : ∃ a b, (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0'] = a ++ b := ⟨(aux (k / 2)), [if k % 2 = 1 then '1' else '0'], rfl⟩
            simp at hc
            -- case: in the prefix
            have in_prefix : (ch ∈ aux (k / 2)) ∨ ch = (if k % 2 = 1 then '1' else '0') := by
              -- List membership in (xs ++ [y]) is either in xs or equal to y
              apply List.mem_append.1; exact hc
            cases in_prefix with
            | inl hin =>
              apply (ihk (k / 2)) (k / 2)
              apply hin
            | inr heq =>
              simp [heq]
              cases (if k % 2 = 1 then Or.inr rfl else Or.inl rfl) with
              | inl _ => exact Or.inl rfl
              | inr _ => exact Or.inr rfl
      -- now apply to n+1
      apply aux_chars (n' + 1)

-- LEMMA: the constructed string has `.data = l` definitionally, so get? reduces to List.get?
-- This allows an easy proof of ValidBitString.
-- LLM HELPER
theorem bits_to_string_valid (l : List Char) (h : ∀ ch ∈ l, ch = '0' ∨ ch = '1') :
  ValidBitString (bits_to_string l) := by
  intro i c hg
  -- `.get?` on a record built as `{ data := l }` reduces to `l.get? i`
  have : (bits_to_string l).get? i = l.get? i := rfl
  rw [this] at hg
  -- now `l.get? i = some c` implies `c ∈ l`, and from the hypothesis on membership we get the claim.
  have : ∃ j, l.get? i = some (l.getElem? i) := by
    -- the previous line is only to hint at the relation; we directly use List.get?_some_iff
    exact (by simp [List.get?] : True)
  -- more directly, use List.get?_some_iff to extract membership
  have mem := List.get?_some_iff.1 hg
  exact h _ mem

-- LEMMA: computing Str
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
/- Helper: convert a natural number to a list of bit characters (MSB first).
   nat_to_bits 0 = ['0']
   nat_to_bits n > 0 = list of '0'/'1' giving binary representation with no leading zeros.
-/
def nat_to_bits : Nat → List Char
  | 0 => ['0']
  | n+1 =>
    let rec aux : Nat → List Char
      | 0 => []
      | k =>
        -- compute bits by recursing on k / 2; this decreases and is accepted by the checker
        let prev := aux (k / 2)
        prev ++ [if k % 2 = 1 then '1' else '0']
    aux (n + 1)

/-- Helper to build a String directly from a list of chars by setting the `.data` field.
    This is convenient because it makes the underlying list equal to `.data` definitionally.
    (We mark it LLM HELPER because it's introduced here to facilitate proofs.) -/
def bits_to_string (l : List Char) : String := { data := l } -- LLM HELPER

-- LEMMA: every character produced by nat_to_bits is '0' or '1'
-- LLM HELPER
theorem nat_to_bits_chars (n : Nat) : ∀ ch ∈ nat_to_bits n, ch = '0' ∨ ch = '1' := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n with
    | zero =>
      simp [nat_to_bits]; intro ch h; simp at h; injection h with h'; subst h'; simp
    | succ n' =>
      dsimp [nat_to_bits]
      let rec aux : Nat → ∀ ch ∈ (@List.nil Char ++ (List.range 0)) → False := fun _ _ => False.elim
      -- We reason about the explicit definition of aux inside nat_to_bits.
      -- Unfolding nat_to_bits gives us the nested aux; we perform a direct argument on its construction.
      let aux_def := nat_to_bits (n' + 1)
      -- Now show every char in aux_def is '0' or '1' by structural reasoning on the helper construction.
      have : ∀ k, (let prev := 
                    let rec aux (k : Nat) : List Char
                      | 0 => []
                      | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
                    aux (k)
                  in prev) = (let rec aux (k : Nat) : List Char
                                | 0 => []
                                | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
                              aux (k)) := by intros; rfl
      clear aux_def aux_def
      -- Now proceed by well-founded induction on the value used inside aux (k).
      have aux_chars : ∀ k, ∀ ch ∈ (let rec aux (k : Nat) : List Char
                                      | 0 => []
                                      | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
                                    aux k), ch = '0' ∨ ch = '1' := by
        intro k
        induction k using Nat.strong_induction_on with
        | ihk k =>
          dsimp
          by_cases h0 : k = 0
          · simp [h0]; intro ch hc; cases hc
          · -- k > 0, list is (aux (k/2)) ++ [bit], use IH for k/2 and the last bit
            dsimp
            intro ch hc
            have : ∃ a b, (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0'] = a ++ b := ⟨(aux (k / 2)), [if k % 2 = 1 then '1' else '0'], rfl⟩
            simp at hc
            -- case: in the prefix
            have in_prefix : (ch ∈ aux (k / 2)) ∨ ch = (if k % 2 = 1 then '1' else '0') := by
              -- List membership in (xs ++ [y]) is either in xs or equal to y
              apply List.mem_append.1; exact hc
            cases in_prefix with
            | inl hin =>
              apply (ihk (k / 2)) (k / 2)
              apply hin
            | inr heq =>
              simp [heq]
              cases (if k % 2 = 1 then Or.inr rfl else Or.inl rfl) with
              | inl _ => exact Or.inl rfl
              | inr _ => exact Or.inr rfl
      -- now apply to n+1
      apply aux_chars (n' + 1)

-- LEMMA: the constructed string has `.data = l` definitionally, so get? reduces to List.get?
-- This allows an easy proof of ValidBitString.
-- LLM HELPER
theorem bits_to_string_valid (l : List Char) (h : ∀ ch ∈ l, ch = '0' ∨ ch = '1') :
  ValidBitString (bits_to_string l) := by
  intro i c hg
  -- `.get?` on a record built as `{ data := l }` reduces to `l.get? i`
  have : (bits_to_string l).get? i = l.get? i := rfl
  rw [this] at hg
  -- now `l.get? i = some c` implies `c ∈ l`, and from the hypothesis on membership we get the claim.
  have : ∃ j, l.get? i = some (l.getElem? i) := by
    -- the previous line is only to hint at the relation; we directly use List.get?_some_iff
    exact (by simp [List.get?] : True)
  -- more directly, use List.get?_some_iff to extract membership
  have mem := List.get?_some_iff.1 hg
  exact h _ mem

-- LEMMA: computing Str
-- </vc-code>

end BignumLean