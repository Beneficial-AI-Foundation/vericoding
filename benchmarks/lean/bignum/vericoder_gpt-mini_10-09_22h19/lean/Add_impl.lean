namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
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
  induction l with
  | nil => rfl
  | cons c cs ih =>
    -- reverse (c :: cs) = reverse cs ++ [c]
    have rev_cons : List.reverse (c :: cs) = List.reverse cs ++ [c] := by
      rw [List.reverse_cons]
    calc
      val_msbf (List.reverse (c :: cs)) = val_msbf (List.reverse cs ++ [c]) := by rw [rev_cons]
      _ = (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (List.reverse cs ++ [c])) := rfl
      _ = (2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (List.reverse cs) + (if c = '1' then 1 else 0)) := by
        -- foldl over append: foldl f b (l ++ [x]) = f (foldl f b l) x
        rw [List.foldl_append]
        -- now reduce foldl on singleton
        simp only [List.foldl]
      _ = (if c = '1' then 1 else 0) + 2 * val_msbf (List.reverse cs) := by ring
      _ = (if c = '1' then 1 else 0) + 2 * val_lsbf cs := by rw [ih]
      _ = val_lsbf (c :: cs) := by simp [val_lsbf]

-- LLM HELPER
theorem val_lsbf_add1 {l : List Char} (h : ∀ c ∈ l, c = '0' ∨ c = '1') :
  val_lsbf (add1_lsbf l) = val_lsbf l + 1 := by
  induction l with
  | nil => simp [add1_lsbf, val_lsbf]
  | cons c cs ih =>
    simp [add1_lsbf]
    by_cases h0 : c = '0'
    · -- c = '0'
      subst h0
      simp [val_lsbf]
    · -- c ≠ '0' hence, using the hypothesis on bits, c must be '1'
      have Hmem : c ∈ c :: cs := by simp
      have := h c Hmem
      cases this with
      | inl hczero => contradiction
      | inr hcone =>
        subst hcone
        -- add1_lsbf (c::cs) = '0' :: add1_lsbf cs
        simp [val_lsbf]
        calc
          val_lsbf ('0' :: add1_lsbf cs) = 0 + 2 * val_lsbf (add1_lsbf cs) := by simp [val_lsbf]
          _ = 2 * (val_lsbf cs + 1) := by
            have ih_prop : ∀ d ∈ cs, d = '0' ∨ d = '1' := by
              intro d hd
              apply h
              simp [List.mem_cons_of_mem] at hd
              exact hd
            rw [ih (fun d hd => ih_prop d hd)]
          _ = val_lsbf ('1' :: cs) + 1 := by simp [val_lsbf]; ring

-- LLM HELPER
theorem add1_preserves_bits {l : List Char} (h : ∀ c ∈ l, c = '0' ∨ c = '1') :
  ∀ c ∈ add1_lsbf l, c = '0' ∨ c = '1' := by
  induction l with
  | nil => simp [add1_lsbf]
  | cons c cs ih =>
    simp [add1_lsbf]
    by_cases h0 : c = '0'
    · intro d hd
      cases hd
      · simp [h0]; left; rfl
      · exact h _ (by simp [hd])
    · -- c ≠ '0', hence must be '1' using h
      have Hmem : c ∈ c :: cs := by simp
      have := h c Hmem
      cases this with
      | inl hczero => contradiction
      | inr hcone =>
        intro d hd
        cases hd
        · simp [hcone]; left; rfl
        · apply ih
          intro x hx
          simp at hx
          exact h x hx

-- LLM HELPER
theorem inc_preserves_bits {l : List Char} (h : ∀ c ∈ l, c = '0' ∨ c = '1') :
  ∀ c ∈ inc_bits l, c = '0' ∨ c = '1' := by
  intro c hc
  unfold inc_bits at hc
  -- membership in reverse corresponds to membership in the underlying list
  have : c ∈ add1_lsbf (List.reverse l) := by
    apply List.mem_reverse.1 hc
  -- show reverse l has the bit property
  have hrev : ∀ d ∈ List.reverse l, d = '0' ∨ d = '1' := by
    intro d hd
    have hr : d ∈ l := List.mem_reverse.1 hd
    exact h _ hr
  apply add1_preserves_bits hrev _ this
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def nat_to_bits (n : Nat) : List Char :=
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
  -- Let n be the numeric sum
  let n := Str2Int s1 + Str2Int s2
  -- helper: Str2Int of bits_to_string equals val_msbf of the bits
  have Str2Int_bits (bits : List Char) : Str2Int (bits_to_string bits) = val_msbf bits := by
    -- Str2Int uses s.data.foldl and String.mk sets .data = bits
    simp [Str2Int, bits_to_string, val_msbf, String.mk]
  -- Show nat_to_bits produces only '0'/'1' characters
  have bits_valid : ∀ m : Nat, ∀ c ∈ nat_to_bits m, c = '0' ∨ c = '1' := by
    intro m
    induction m with
    | zero =>
      intro c hc
      simp [nat_to_bits] at hc
      cases hc with
      | head => left; rfl
      | tail => contradiction
    | succ k ih =>
      -- nat_to_bits (k+1) = inc_bits (nat_to_bits k)
      intro c hc
      simp [nat_to_bits] at hc
      -- apply inc_preserves_bits with the induction hypothesis ih
      apply inc_preserves_bits
      exact ih
  -- Show numeric value of nat_to_bin m equals m
  have bits_value : ∀ m : Nat, Str2Int (nat_to_bin m) = m := by
    intro m
    induction m with
    | zero =>
      simp [nat_to_bin, nat_to_bits, bits_to_string, Str2Int]
      -- nat_to_bits 0 = ['0'], Str2Int of that is 0
      simp [val_msbf]
    | succ k ih =>
      -- use relation between string and val_msbf
      have H1 : Str2Int (nat_to_bin (k + 1)) = val_msbf (nat_to_bits (k + 1)) := by
        simp [nat_to_bin, bits_to_string, Str2Int, val_msbf]
      have H2 : val_msbf (nat_to_bits (k + 1)) = val_msbf (inc_bits (nat_to_bits k)) := by
        simp [nat_to_bits]
      have H3 : val_msbf (inc_bits (nat_to_bits k)) = val_msbf (nat_to_bits k) + 1 := by
        apply val_msbf_inc_bits
        intro c hc
        apply (bits_valid k) c hc
      have H4 : val_msbf (nat_to_bits k) = Str2Int (nat_to_bin k) := by
        simp [nat_to_bin, bits_to_string, Str2Int, val_msbf]
      calc
        Str2Int (nat_to_bin (k + 1)) = val_msbf (nat_to_bits (k + 1)) := H1
        _ = val_msbf (inc_bits (nat_to_bits k)) := by rw [H2]
        _ = val_msbf (nat_to_bits k) + 1 := by rw [H3]
        _ = Str2Int (nat_to_bin k) + 1 := by rw [H4]
        _ = k + 1 := by rw [ih]
  -- Now finish the theorem: Add s1 s2 = nat_to_bin n
  dsimp [Add, n]
  -- ValidBitString of the result follows from bits_valid
  have A : ∀ i c, (bits_to_string (nat_to_bits n)).get? i = some c → (c = '0' ∨ c = '1') := by
    intro i c h
    simp [bits_to_string, String.mk] at h
    -- convert get? to membership in the underlying list
    have mem : c ∈ nat_to_bits n := by
      -- List.get?_mem: from get? we obtain membership
      exact (List.get?_mem.2 h)
    apply (bits_valid n) c mem
  -- Combine membership property to form ValidBitString predicate and numeric equality
  constructor
  · -- ValidBitString
    intro i c h
    apply A; assumption
  · -- numeric equality
    simp [Add]
    calc
      Str2Int (Add s1 s2) = Str2Int (nat_to_bin n) := rfl
      _ = n := by apply bits_value
      _ = Str2Int s1 + Str2Int s2 := rfl
-- </vc-proof>

end BignumLean