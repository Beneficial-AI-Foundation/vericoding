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
  | nil => simp [val_msbf, val_lsbf]
  | cons c cs ih =>
    -- reverse (c :: cs) = reverse cs ++ [c]
    have rev_cons : List.reverse (c :: cs) = List.reverse cs ++ [c] := by
      simp [List.reverse]
    -- foldl over append: foldl f 0 (xs ++ [y]) = f (foldl f 0 xs) y
    calc
      val_msbf (List.reverse (c :: cs)) = val_msbf (List.reverse cs ++ [c]) := by rw [rev_cons]
      _ = (val_msbf (List.reverse cs) * 2 + (if c = '1' then 1 else 0)) := by
        -- use List.foldl_append specialized to singleton appendix
        -- List.foldl_append works for general append; here we apply it then simplify.
        have : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (List.reverse cs ++ [c])
            = (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (List.reverse cs)).foldl (fun acc ch => acc) c := by
          -- This auxiliary equality is just a stepping stone; we won't rely on it.
          simp [List.foldl_append]
        simp [val_msbf, List.foldl_append]
      _ = (if c = '1' then 1 else 0) + 2 * val_msbf (List.reverse cs) := by
        ring
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
          _ = 2 * (val_lsbf cs + 1) := by rw [ih]; exact fun d hd => h d (by simp [hd])
          _ = (if '1' = '1' then 1 else 0) + 2 * val_lsbf cs + 1 := by ring
          _ = val_lsbf ('1' :: cs) + 1 := by simp [val_lsbf]

-- LLM HELPER
theorem val_msbf_inc_bits (bits : List Char) (hbits : ∀ c ∈ bits, c = '0' ∨ c = '1') :
  val_msbf (inc_bits bits) = val_msbf bits + 1 := by
  -- inc_bits bits = reverse (add1_lsbf (reverse bits))
  unfold inc_bits
  -- val_msbf (reverse xs) = val_lsbf xs
  have H1 : val_msbf (List.reverse (add1_lsbf (List.reverse bits))) = val_lsbf (add1_lsbf (List.reverse bits)) := by
    apply val_msbf_rev_eq_val_lsbf
  have H2 : val_lsbf (add1_lsbf (List.reverse bits)) = val_lsbf (List.reverse bits) + 1 := by
    -- need to show elements of reverse bits are '0'/'1'
    have hrev : ∀ c ∈ List.reverse bits, c = '0' ∨ c = '1' := by
      intro c hc
      have hr : c ∈ bits := List.mem_reverse.1 hc
      exact hbits _ hr
    apply val_lsbf_add1 hrev
  have H3 : val_lsbf (List.reverse bits) = val_msbf (List.reverse (List.reverse bits)) := by
    apply val_msbf_rev_eq_val_lsbf
  calc
    val_msbf (inc_bits bits) = val_msbf (List.reverse (add1_lsbf (List.reverse bits))) := rfl
    _ = val_lsbf (add1_lsbf (List.reverse bits)) := by rw [val_msbf_rev_eq_val_lsbf]
    _ = val_lsbf (List.reverse bits) + 1 := by rw [H2]
    _ = val_msbf (List.reverse (List.reverse bits)) + 1 := by rw [← val_msbf_rev_eq_val_lsbf (List.reverse bits)]
    _ = val_msbf bits + 1 := by simp

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
          have : x ∈ cs := by simpa using hx
          exact h x this

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
    have hr : d ∈ l := List.mem_reverse.1 hd |> (fun h' => h')
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
  -- Show nat_to_bits produces only '0'/'1' characters and its numeric value equals n.
  have bits_valid : ∀ m : Nat, (∀ c ∈ nat_to_bits m, c = '0' ∨ c = '1') := by
    intro m
    induction m with
    | zero => simp [nat_to_bits]
    | succ k ih =>
      simp [nat_to_bits]
      -- nat_to_bits (k+1) = inc_bits (nat_to_bits k)
      -- use inc_preserves_bits with the induction hypothesis
      apply inc_preserves_bits
      intro c hc
      apply ih
  have bits_value : ∀ m : Nat, Str2Int (nat_to_bin m) = m := by
    intro m
    induction m with
    | zero => simp [nat_to_bin, nat_to_bits, bits_to_string, Str2Int, val_msbf]
    | succ k ih =>
      simp [nat_to_bin, nat_to_bits]
      -- nat_to_bits (k+1) = inc_bits (nat_to_bits k)
      -- use Str2Int_bits and val_msbf_inc_bits
      have Hbits := bits_valid k
      have Hval_inc := val_msbf_inc_bits (nat_to_bits k) (fun c hc => Hbits _ hc)
      calc
        Str2Int (nat_to_bin (k + 1)) = val_msbf (nat_to_bits (k + 1)) := by
          simp [nat_to_bin, bits_to_string, Str2Int, val_msbf]
        _ = val_msbf (inc_bits (nat_to_bits k)) := by simp [nat_to_bits]
        _ = val_msbf (nat_to_bits k) + 1 := by exact Hval_inc
        _ = Str2Int (nat_to_bin k) + 1 := by
          simp [nat_to_bin, bits_to_string, Str2Int, val_msbf]
        _ = k + 1 := by rw [ih]
  -- Now finish the theorem: Add s1 s2 = nat_to_bin n
  dsimp [Add, n]
  -- ValidBitString of the result follows from bits_valid
  have A : (∀ i c, (bits_to_string (nat_to_bits n)).get? i = some c → (c = '0' ∨ c = '1')) := by
    intro i c h
    -- for String.mk, .data = nat_to_bits n, and get? corresponds to nth? on data
    have : c ∈ nat_to_bits n := by
      -- convert get? to membership: for String.mk, get? returns some c when nth? on data holds
      -- We can use List.nth?_mem lemma style: get? i = some c -> c ∈ bits
      -- We'll prove by a small observation: if get? yields c then c is in data.
      -- Use the fact that String.mk uses List.toString? but simpler: use membership via list
      -- Instead of relating get?, we can show a stronger statement by using bits_valid for all elements.
      -- We avoid converting get? to mem by noting get? some c implies c is one of the characters produced
      -- Use the trivial fact: from get? = some c, c must be in .data.
      have : c ∈ (bits_to_string (nat_to_bits n)).data := by
        -- unfold bits_to_string and String.mk
        simp [bits_to_string, String.mk] at h
        -- now h is of the form List.get? ... = some c; from that get? implies membership
        -- Use List.get?_mem: if List.get? xs i = some c then c ∈ xs
        exact List.get?_mem.2 h
      -- data = nat_to_bits n
      simp [bits_to_string, String.mk] at this
      exact this
    exact (bits_valid n) _ this
  -- Combine membership property to form ValidBitString predicate
  constructor
  · -- ValidBitString
    intro i c h
    apply A; assumption
  · -- numeric equality
    show Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2
    simp [Add]
    -- Add s1 s2 = nat_to_bin n, and Str2Int (nat_to_bin n) = n, by bits_value
    calc
      Str2Int (Add s1 s2) = Str2Int (nat_to_bin n) := rfl
      _ = n := by apply bits_value
      _ = Str2Int s1 + Str2Int s2 := rfl
-- </vc-proof>

end BignumLean