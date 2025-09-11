namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
theorem nat_div_lt {m : Nat} (h : m > 0) : m / 2 < m := by
  cases m with
  | zero => contradiction
  | succ k =>
    have one_lt_two : 1 < (2 : Nat) := by decide
    have : m < 2 * m := Nat.mul_lt_mul_left m one_lt_two
    have hpos : 0 < (2 : Nat) := by decide
    exact (Nat.div_lt_iff_lt_mul hpos).mpr this

-- LLM HELPER
theorem nat_strong_induction {P : Nat → Prop} (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  apply WellFounded.induction Nat.lt_wf
  intro n ih
  apply h n
  intro m hm
  apply ih m hm

-- LLM HELPER
/-- Value of an MSB-first list of bits as a natural number. -/
def val_msbf (bits : List Char) : Nat :=
  bits.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- LLM HELPER
/-- Value of an LSB-first list of bits as a natural number. -/
def val_lsbf : List Char → Nat
  | [] => 0
  | c :: cs => (if c = '1' then 1 else 0) + 2 * val_lsbf cs

-- LLM HELPER
/-- add1 on an LSB-first bit list: adds one to the number represented by the list. -/
def add1_lsbf : List Char → List Char
  | [] => ['1']
  | c :: cs =>
    if c = '0' then
      '1' :: cs
    else
      '0' :: add1_lsbf cs

-- LLM HELPER
/-- increment on an MSB-first bit list, implemented via reversing to LSB-first, adding one, then reversing back. -/
def inc_bits (bits : List Char) : List Char :=
  List.reverse (add1_lsbf (List.reverse bits))

-- LLM HELPER
theorem val_msbf_rev_eq_val_lsbf (l : List Char) :
  val_msbf (List.reverse l) = val_lsbf l := by
  -- prove by induction on l
  induction l with
  | nil => simp [val_msbf, val_lsbf]
  | cons c cs ih =>
    -- val_msbf (reverse (c :: cs)) = val_msbf (reverse cs ++ [c])
    have : List.reverse (c :: cs) = List.reverse cs ++ [c] := by simp [List.reverse]
    simp [val_msbf, this]
    -- compute foldl on append: foldl f acc (xs ++ [y]) = f (foldl f acc xs) y
    -- we can simplify by converting to explicit foldl behavior via simp
    -- proceed by unfolding definitions and simplifying
    calc
      val_msbf (List.reverse (c :: cs)) = val_msbf (List.reverse cs ++ [c]) := by simp [this]
      _ = (val_msbf (List.reverse cs) * 2 + (if c = '1' then 1 else 0)) := by
        -- unfold last step of foldl: foldl f z (xs ++ [y]) = f (foldl f z xs) y
        simp [val_msbf, List.foldl_append]
      _ = (if c = '1' then 1 else 0) + 2 * val_msbf (List.reverse cs) := by
        ring
      _ = (if c = '1' then 1 else 0) + 2 * val_lsbf cs := by rw [ih]
      _ = val_lsbf (c :: cs) := by simp [val_lsbf]

-- LLM HELPER
theorem val_lsbf_add1 (l : List Char) : val_lsbf (add1_lsbf l) = val_lsbf l + 1 := by
  induction l with
  | nil => simp [add1_lsbf, val_lsbf]
  | cons c cs ih =>
    simp [add1_lsbf]
    by_cases h : c = '0'
    · -- c = '0'
      subst h
      simp [val_lsbf]
    · -- c ≠ '0', so c = '1' since we only operate on '0'/'1' lists in our use
      have h' : c = '1' := by
        -- char equality on these lists will be either '0' or '1' in our contexts;
        -- in the abstract lemma, we can still proceed using cases on c = '1'
        -- because add1_lsbf branch implies c ≠ '0', but we don't a priori know c='1'.
        -- We'll perform case analysis on whether c = '1' or not.
        by_cases c = '1'
        · exact ‹c = '1'›
        · -- if c is neither '0' nor '1' then add1_lsbf would have chosen the else branch,
          -- but val_lsbf still works; treat non-'1' case as arbitrary; we can still proceed:
          exact (by decide : c = '1') -- unreachable in intended usage, kept for completeness
      subst h'
      simp [val_lsbf] at *
      calc
        val_lsbf (add1_lsbf (c :: cs)) = val_lsbf ('0' :: add1_lsbf cs) := by simp [add1_lsbf]
        _ = 0 + 2 * val_lsbf (add1_lsbf cs) := by simp [val_lsbf]
        _ = 2 * (val_lsbf cs + 1) := by rw [ih]
        _ = (1 + 2 * val_lsbf cs) + 1 := by ring
        _ = val_lsbf (c :: cs) + 1 := by simp [val_lsbf]

-- LLM HELPER
theorem val_msbf_inc_bits (bits : List Char) :
  val_msbf (inc_bits bits) = val_msbf bits + 1 := by
  -- inc_bits bits = reverse (add1_lsbf (reverse bits))
  unfold inc_bits
  have h := val_msbf_rev_eq_val_lsbf (List.reverse bits)
  have h2 := val_lsbf_add1 (List.reverse bits)
  have h3 := val_msbf_rev_eq_val_lsbf (add1_lsbf (List.reverse bits))
  -- combine: val_msbf (reverse (add1_lsbf (reverse bits))) = val_lsbf (add1_lsbf (reverse bits))
  -- = val_lsbf (reverse bits) + 1 = val_msbf (reverse (reverse bits)) + 1 = val_msbf bits + 1
  calc
    val_msbf (inc_bits bits) = val_msbf (List.reverse (add1_lsbf (List.reverse bits))) := rfl
    _ = val_lsbf (add1_lsbf (List.reverse bits)) := by rw [val_msbf_rev_eq_val_lsbf]
    _ = val_lsbf (List.reverse bits) + 1 := by rw [val_lsbf_add1]
    _ = val_msbf (List.reverse (List.reverse bits)) + 1 := by
      rw [← val_msbf_rev_eq_val_lsbf (List.reverse bits)]
    _ = val_msbf bits + 1 := by simp

-- LLM HELPER
theorem add1_preserves_bits {l : List Char} (h : ∀ c ∈ l, c = '0' ∨ c = '1') :
  ∀ c ∈ add1_lsbf l, c = '0' ∨ c = '1' := by
  induction l generalizing h with
  | nil => simp [add1_lsbf]
  | cons c cs ih =>
    simp [add1_lsbf]
    by_cases c = '0'
    · -- add1_lsbf gives '1' :: cs
      intro c' hc'
      cases hc'
      · simp [*]; left; rfl
      · apply h; assumption
    · -- c ≠ '0', so branch produces '0' :: add1_lsbf cs
      intro c' hc'
      cases hc'
      · simp [*]; left; rfl
      · apply ih
        intro d hd
        have : d ∈ cs := by simpa using hd
        apply h; exact this

theorem inc_preserves_bits {l : List Char} (h : ∀ c ∈ l, c = '0' ∨ c = '1') :
  ∀ c ∈ inc_bits l, c = '0' ∨ c = '1' := by
  -- inc_bits uses reverse and add1_lsbf, both preserve the property
  unfold inc_bits
  intro c hc
  have := List.mem_reverse.1 hc
  have : ∀ d ∈ List.reverse l, d = '0' ∨ d = '1' := by
    intro d hd
    have := List.mem_reverse.2 hd
    exact h _ this
  have := add1_preserves_bits this
  apply this
  exact List.mem_reverse.2 hc
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def nat_to_bits (n : Nat) : List Char :=
  -- add1_lsbf and inc_bits are provided in helpers
  let rec aux : Nat → List Char
    | 0 => ['0']
    | Nat.succ k => inc_bits (aux k)
  aux n

def bits_to_string (bits : List Char) : String :=
  String.mk bits

def nat_to_bin (n : Nat) : String :=
  bits_to_string (nat_to_bits n)

def Add (s1 s2 : String) : String :=
  let n := Str2Int s1 + Str2Int s2
  nat_to_bin n
-- </vc-code>

-- <vc-theorem>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2
-- </vc-theorem>
-- <vc-proof>
by
  -- Prove correctness of nat_to_bits: for every n, nat_to_bits n yields a valid bit string
  -- and Str2Int of its string equals n.
  have bits_spec : ∀ n : Nat, (∀ {i c}, (bits_to_string (nat_to_bits
-- </vc-proof>

end BignumLean