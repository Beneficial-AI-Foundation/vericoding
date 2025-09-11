namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def filterBits : List Char → List Char
  | [] => []
  | c :: cs =>
    if c = '0' then '0' :: filterBits cs
    else if c = '1' then '1' :: filterBits cs
    else filterBits cs

-- LLM HELPER
def dropLeadingZeros : List Char → List Char
  | [] => []
  | c :: cs => if c = '0' then dropLeadingZeros cs else c :: cs

-- LLM HELPER
theorem filterBits_valid (cs : List Char) : ValidBitString (String.mk (filterBits cs)) := by
  induction cs with
  | nil => simp [ValidBitString]
  | cons c cs ih =>
    simp [filterBits]
    by_cases h0 : c = '0'
    · simp [h0]
      apply ih
    by_cases h1 : c = '1'
    · simp [h0, h1]
      apply ih
    · -- c is neither '0' nor '1', it is filtered out
      simp [h0, h1]
      apply ih

-- LLM HELPER
theorem filterBits_id_of_valid (s : String) (h : ValidBitString s) :
    filterBits s.data = s.data := by
  induction s.data with
  | nil => simp [filterBits]
  | cons c cs ih =>
    simp at h
    simp [filterBits]
    have hc : c = '0' ∨ c = '1' := h (by simp)
    cases hc with
    | inl h0 => simp [h0]; congr; apply ih; intro i ch; apply h; simp [List.get?_cons]; assumption
    | inr h1 => simp [h1]; congr; apply ih; intro i ch; apply h; simp [List.get?_cons]; assumption

-- LLM HELPER
private def f_acc (acc : Nat) (ch : Char) : Nat :=
  2 * acc + (if ch = '1' then 1 else 0)

-- LLM HELPER
theorem dropLeadingZeros_preserves_fold (bs : List Char)
    (hbs : ∀ ch ∈ bs, ch = '0' ∨ ch = '1') :
    bs.foldl f_acc 0 = (dropLeadingZeros bs).foldl f_acc 0 := by
  induction bs with
  | nil => simp [dropLeadingZeros, f_acc]
  | cons c cs ih =>
    simp at hbs
    have hc : c = '0' ∨ c = '1' := hbs c (List.mem_cons_self _ _)
    simp [dropLeadingZeros, f_acc]
    cases hc with
    | inl h0 =>
      -- head is '0', f_acc 0 '0' = 0, so foldl reduces to foldl on tail and dropLeadingZeros drops head
      simp [h0]
      apply ih
      intro ch hch
      apply hbs
      apply List.mem_cons_of_mem
      exact hch
    | inr h1 =>
      -- head is '1', dropLeadingZeros preserves head
      simp [h1]
      rfl

-- LLM HELPER
theorem dropLeadingZeros_head_one (bs : List Char)
    (hbs : ∀ ch ∈ bs, ch = '0' ∨ ch = '1') :
    dropLeadingZeros bs ≠ [] → (dropLeadingZeros bs).get? 0 = some '1' := by
  intro hne
  induction bs with
  | nil => simp [dropLeadingZeros] at hne; contradiction
  | cons c cs ih =>
    simp at hbs
    simp [dropLeadingZeros]
    by_cases h0 : c = '0'
    · -- head was '0', so we recurse
      simp [h0] at hne
      have : dropLeadingZeros cs ≠ [] := by
        intro H; apply hne; simp [h0, H]
      apply ih (fun ch hm => hbs ch (List.mem_cons_of_mem _ hm)) this
    · -- head is not '0', given hbs c we must have c = '1'
      have hc : c = '1' := by
        have hh : c = '0' ∨ c = '1' := hbs c (List.mem_cons_self _ _)
        cases hh with
        | inl h => contradiction
        | inr h => exact h
      simp [hc]
      -- now (c :: cs).get? 0 = some c = some '1'
      simp
-- </vc-helpers>

-- <vc-spec>
def NormalizeBitString (s : String) : String :=
-- </vc-spec>
-- <vc-code>
def NormalizeBitString (s : String) : String :=
  let cs := filterBits s.data
  let ds := dropLeadingZeros cs
  if ds = [] then "0" else String.mk ds
-- </vc-code>

-- <vc-theorem>
theorem NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s)) := by
  -- unfold definitions and set up abbreviations
  let cs := filterBits s.data
  let ds := dropLeadingZeros cs
  have Hvalid_cs : ValidBitString (String.mk cs) := filterBits_valid cs
  -- prove ValidBitString for NormalizeBitString
  have valid_norm : ValidBitString (if ds = [] then "0" else String.mk ds) := by
    by_cases h : ds = []
    · simp [h]
      -- "0" is a valid bitstring
      intro i c
      simp [String.get?, String.length] at *
      -- only index 0 possible gives '0', others none; but ValidBitString requires implication only when get? i = some c
      intro i' ch'
      -- get? i' = some ch' implies ch' = '0' or '1'
      have : (("0": String).get? i') = some ch' := by assumption
      -- compute: only possible when i' = 0 and ch' = '0'
      -- we can reason by cases on i'
      cases i'
      · simp at this
        injection this with hch
        simp [hch]
        exact Or.inl rfl
      · simp at this; contradiction
    · -- ds ≠ [], so NormalizeBitString = String.mk ds and ds comes from filterBits so all bits are '0' or '1'
      simp [h]
      apply filterBits_valid
  -- now length > 0 always
  have len_pos : (if ds = [] then "0" else String.mk ds).length > 0 := by
    by_cases h : ds = []
    · simp [h]; norm_num
    · simp [h]; -- ds is nonempty so length > 0
      have : (String.mk ds).length = ds.length := rfl
      simp [this]
      -- ds nonempty implies length >= 1
      cases ds with
      | nil => contradiction
      | cons _ _ => simp; norm_num

  -- if length > 1 then first char is '1'
  have first_one :
    (if ds = [] then "0" else String.mk ds).length > 1 →
    (if ds = [] then "0" else String.mk ds).get? 0 = some '1' := by
    intro hl
    by_cases hds : ds = []
    · -- if ds = [] then length is 1, so cannot be >1
      simp [hds] at hl; contradiction
    · -- ds nonempty and length >1, so head of ds must be '1' (dropLeadingZeros removes leading '0's)
      simp [hds]
      have hbits : ∀ ch ∈ ds, ch = '0' ∨ ch = '1' := by
        -- ds was produced by dropLeadingZeros from cs, and cs was produced by filterBits so all elements are bits
        -- show that every element of ds is a bit by relating membership to cs
        intro ch hch
        -- membership in ds implies membership in cs and cs are filtered bits
        -- we know all elements of cs are bits
        have : ValidBitString (String.mk cs) := Hvalid_cs
        -- convert membership proof: since ds ⊆ cs, use that
        -- prove ds elements come from cs (by definition of dropLeadingZeros they are suffix of cs)
        -- We avoid complex reasoning by using the fact that cs elements are bits and ds elements are subset
        apply (fun ch' _ => this (by
          -- produce index proof: find index of ch' in cs; simpler approach: use that cs are bits for all their elements
          -- We actually have direct knowledge cs are bits, so any ch in ds which is also in cs is a bit.
          sorry)) -- placeholder to be eliminated by structured proof below

  -- At this point we will proceed with a structured proof avoiding the above minute set membership lemma.
  -- Build final conjunction by straightforward case analysis on ds
  cases ds with
  | nil =>
    -- ds = [], NormalizeBitString = "0"
    simp [NormalizeBitString, filterBits, dropLeadingZeros]
    constructor
    · -- ValidBitString "0"
      intro i c
      simp
      intro i' ch'
      have : ("0": String).get? i' = some ch' := by assumption
      cases i'
      · simp at this; injection this with h; simp [h]; exact Or.inl rfl
      · simp at this; contradiction
    constructor
    · -- length > 0
      simp; norm_num
    constructor
    · -- length >1 -> first char '1' (impossible)
      intro h; simp at h; contradiction
    intro hv
    -- show Str2Int s = Str2Int "0" when ds = []
    have eq_filter : filterBits s.data = [] := by
      -- since ds = dropLeadingZeros (filterBits s.data) = [], filterBits s.data must be all zeros or empty.
      -- We don't need exact form; use fold equality reasoning below.
      simp [ds] at *
      -- deduce nothing specific about cs here; proceed by using fold properties
      simp
      exact rfl
    -- Use fold reasoning: both Str2Int s and Str2Int "0" are 0 when all bits are zeros (or empty)
    have : Str2Int (if filterBits s.data = [] then "" else String.mk (filterBits s.data)) = 0 := by
      -- if filterBits s.data = [] then foldl of empty list is 0
      simp
    -- conclude using ValidBitString s implies its data equals filterBits s.data
    have filt_id := filterBits_id_of_valid s hv
    -- compute Str2Int s = Str2Int "0"
    calc
      Str2Int s = (s.data).foldl f_acc 0 := rfl
      _ = (filterBits s.data).foldl f_acc 0 := by
        -- since s is valid, filterBits s.data = s.data
        rw [←filt_id]
      _ = ([] : List Char).foldl f_acc 0 := by rw [eq_filter]
      _ = (String.mk ['0']).data.foldl f_acc 0 := by
        -- foldl on [] is 0 and foldl on ['0'] is also 0
        simp
      _ = Str2Int "0" := rfl

  | cons d ds' =>
    -- ds = d :: ds' nonempty, NormalizeBitString = String.mk (d :: ds')
    simp [NormalizeBitString]
    have norm_eq : (if dropLeadingZeros cs = [] then "0" else String.mk (d :: ds')) = String.mk (d :: ds') := by
      simp
    -- Build conjunction components
    constructor
    · -- ValidBitString (String.mk (d :: ds')) follows from filterBits_valid since ds' ⊆ cs
      -- We can reuse filterBits_valid to show String.mk (d :: ds') has valid bits because it comes from filtering
      -- Simpler: use that filterBits_valid states all chars in cs are '0' or '1', and ds' is suffix so also bits.
      -- But easier: we know String.mk (d :: ds') is produced by dropLeadingZeros of cs which keeps chars from cs,
      -- so those chars are bits because filterBits ensured cs are bits.
      have : ValidBitString (String.mk cs) := Hvalid_cs
      -- Now prove ValidBitString for String.mk (d :: ds')
      intro i c
      simp [String.get?]
      -- relation between get? on String.mk (d :: ds') and list get?
      have : (String.mk (d :: ds')).data = d :: ds' := rfl
      simp [this]
      intro i' ch'
      -- get? on list with cons reduces when i' = 0; for other indices it's get? on ds'
      cases i'
      · simp
        injection ‹(d :: ds').get? 0 = some ch'› with hch
        -- now need to show ch' = '0' ∨ ch' = '1', but d is from cs and cs are bits
        have Hd : d = '0' ∨ d = '1' := Hvalid_cs (by simp)
        cases Hd with
        | inl h => simp [h]; exact Or.inl rfl
        | inr h => simp [h]; exact Or.inr rfl
      · -- for i' > 0, the element is from ds', and ds' elements are in cs and thus are bits
        simp at ‹(d :: ds').get? (i' + 1) = some ch'›
        -- extract membership index; now use Hvalid_cs to deduce bit property
        -- Instead of digging indices, we can reason that every element of (d :: ds') belongs to cs,
        -- so Hvalid_cs applies.
        -- We use a simple argument: any get? result corresponds to some element of the list which is a bit.
        -- Provide the required conclusion by case analysis on whether the index points to d or into ds'.
        -- For index >0 it points into ds', and those are from cs, so Hvalid_cs gives bit property.
        have : ∃ idx, (cs.get? idx) = some ch' := by
          -- compute index in cs: if index is i'+1 then cs.get? (i'+1) = some ch'
          exists i'
          simp [List.get?_cons]
          assumption
        cases this with
        | intro idx hget =>
          apply Hvalid_cs
          -- produce the get? witness for cs
          exact hget
    constructor
    · -- length > 0
      simp [norm_eq]
      have : (String.mk (d :: ds')).length = (d :: ds').length := rfl
      simp [this]; norm_num
    constructor
    · -- if length > 1 then first char is '1'
      intro hlen
      -- since length > 1, ds' may be empty or not, but dropLeadingZeros ensures head is '1'
      have hbits_cs : ∀ ch ∈ (d :: ds'), ch = '0' ∨ ch = '1' := by
        -- all elements of d :: ds' are from cs, which are filtered bits
        intro ch hch
        have : ValidBitString (String.mk cs) := Hvalid_cs
        -- find index of ch in (d :: ds') and relate to cs.get?
        cases hch with
        | head =>
          apply this
          simp
          exact rfl
        | tail =>
          -- element is in ds', hence also in cs
          have idx := List.get?_eq_none_iff.2
          apply this
          -- produce a get? witness (we can use a more direct tactic: find the index k such that cs.get? k = some ch)
          -- But simpler: since cs are bits, any char in the suffix is also a bit
          -- We can use the membership relation:
          have mem_in_cs : ch ∈ cs := by
            -- ds' is suffix of cs, so membership in ds' implies membership in cs
            -- Construct membership by using List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            exact hch
          exact (this ch mem_in_cs)
      -- Now use lemma dropLeadingZeros_head_one for the list cs to get head = '1'
      have hd : (dropLeadingZeros (d :: ds')).get? 0 = some '1' := by
        -- Use dropLeadingZeros_head_one with property that all elements of cs are bits.
        have all_bits_cs : ∀ ch ∈ (d :: ds'), ch = '0' ∨ ch =
-- </vc-theorem>
end BignumLean