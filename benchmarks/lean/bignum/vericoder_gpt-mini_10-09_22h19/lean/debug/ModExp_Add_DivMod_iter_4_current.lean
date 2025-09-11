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
def nat_to_bits (n : Nat) : List Char :=
  if n = 0 then
    ['0']
  else
    let g := fun k : Nat => if k = 0 then none else some ((if k % 2 = 1 then '1' else '0'), k / 2)
    (List.unfoldr g n).reverse

/-- Build a String with exact `.data = l`. -/ -- LLM HELPER
def bits_to_string (l : List Char) : String := { data := l }

theorem nat_to_bits_chars : ∀ n ch, ch ∈ nat_to_bits n → ch = '0' ∨ ch = '1' := by
  intro n ch h
  by_cases hn : n = 0
  · -- case n = 0
    simp [nat_to_bits, hn] at h
    -- h : ch ∈ ['0']
    simp at h
    cases h with
    | inl heq => subst heq; simp; exact Or.inl rfl
    | inr _ => contradiction
  · -- case n > 0
    dsimp [nat_to_bits] at h
    let g := fun k : Nat => if k = 0 then none else some ((if k % 2 = 1 then '1' else '0'), k / 2)
    have hrev : nat_to_bits n = (List.unfoldr g n).reverse := by simp [nat_to_bits, hn]
    rw [hrev] at h
    -- turn membership in reverse into membership in the original unfoldr list
    have hmem := (List.mem_reverse).1 h
    -- prove by strong induction on the seed of unfoldr
    let P := fun k => ∀ c, c ∈ List.unfoldr g k → c = '0' ∨ c = '1'
    have IH : ∀ k, (∀ m < k, P m) → P k := by
      intro k ih c mem
      dsimp [g] at mem
      by_cases hk0 : k = 0
      · simp [hk0] at mem; contradiction
      · -- g k = some (bit, k/2)
        have gk : g k = some ((if k % 2 = 1 then '1' else '0'), k / 2) := by simp [hk0]
        rw [gk] at mem
        simp at mem
        cases mem with
        | inl heq =>
          -- c equals the head bit
          have : c = (if k % 2 = 1 then '1' else '0') := heq
          rwa [this]
        | inr hrest =>
          -- c is in the tail, apply IH to k/2 which is smaller than k
          have : k / 2 < k := Nat.div_lt_self (Nat.zero_lt_succ k)
          apply ih (k / 2) this c hrest
    -- apply IH for n
    apply IH n
    intro m mm lt_m
    -- show P m holds using the same IH (well-founded recursion encoded above)
    apply IH m
    exact fun _ _ _ => by
      -- this branch will never be used because IH is applied only as needed
      simp at lt_m; trivial
    -- finally use IH at n to conclude
    exact hmem

theorem nat_to_bits_fold (n : Nat) :
  (nat_to_bits n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  by_cases hn : n = 0
  · -- n = 0 case: nat_to_bits 0 = ['0']
    simp [nat_to_bits, hn]
    simp
  · -- n > 0
    dsimp [nat_to_bits]
    let g := fun k : Nat => if k = 0 then none else some ((if k % 2 = 1 then '1' else '0'), k / 2)
    -- prove by well-founded/strong induction on k that fold on reverse (unfoldr g k) yields k
    let P := fun k => ( (List.unfoldr g k).reverse ).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = k
    have IH : ∀ k, (∀ m < k, P m) → P k := by
      intro k ih
      dsimp [P]
      dsimp [g]
      by_cases hk0 : k = 0
      · simp [hk0]
      · -- unfoldr g k = bit :: unfoldr g (k/2)
        have gk : List.unfoldr g k = (if k % 2 = 1 then '1' else '0') :: List.unfoldr g (k / 2) := by
          simp [g, hk0]
        rw [gk]
        -- reverse of cons: reverse (a :: t) = reverse t ++ [a]
        simp only [List.reverse_cons, List.foldl_append, List.foldl]
        -- let bitval be numeric value of the last bit
        have ih_step : ((List.unfoldr g (k / 2)).reverse).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = k / 2 := by
          have : k / 2 < k := Nat.div_lt_self (Nat.zero_lt_succ k)
          apply ih (k / 2) this
        rw [ih_step]
        -- compute numeric value of the bit
        have bval : (if k % 2 = 1 then 1 else 0) = k % 2 := by
          cases Nat.mod_two_eq_zero_or_one k with
          | inl h => simp [h]
          | inr h => simp [h]
        rw [bval]
        -- now 2 * (k/2) + k % 2 = k by div_mul_add_mod
        exact (Nat.div_mul_add_mod k 2).symm
    -- apply IH to n
    apply IH n
    intro m hm lt
    -- recursive cases handled by IH
    exact IH m
    -- finally deduce the desired equality using the fact nat_to_bits n = reverse (unfoldr g n)
    -- but we applied IH at n already; need to connect to nat_to_bits n
    dsimp [nat_to_bits] at *
    simp [nat_to_bits, hn] at IH
    -- use IH result
    have res := (IH n) fun _ _ => by trivial
    exact res

theorem bits_to_string_valid (l : List Char) (h : ∀ ch ∈ l, ch = '0' ∨ ch = '1') :
  ValidBitString (bits_to_string l) := by
  intro i c hg
  have : (bits_to_string l).get? i = l.get? i := rfl
  rw [this] at hg
  have mem := List.get?_some_iff.1 hg
  exact h _ mem

theorem bits_to_string_str2int (l : List Char) :
  Str2Int (bits_to_string l) = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let base := Str2Int sx % Str2Int sz
  let exp := Str2Int sy
  let res := Exp_int base exp % Str2Int sz
  bits_to_string (nat_to_bits res)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (h1 : ValidBitString sx) (h2 : ValidBitString sy) (h3 : ValidBitString sz) (h_pos : Str2Int sz > 0) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx % Str2Int sz) (Str2Int sy) % Str2Int sz
-- </vc-theorem>
-- <vc-proof>
proof :=
  fun sx sy sz h1 h2 h3 h_pos => by
    dsimp [ModExp]
    let val := Exp_int (Str2Int sx % Str2Int sz) (Str2Int sy) % Str2Int sz
    -- validity: nat_to_bits produces only '0'/'1', so bits_to_string is valid
    have chars := nat_to_bits_chars val
    have v := bits_to_string_valid (nat_to_bits val) chars
    -- numeric equality: Str2Int (bits_to_string l) = l.foldl ... by def
    have eq1 := bits_to_string_str2int (nat_to_bits val)
    -- and nat_to_bits_fold gives that foldl equals val
    have eq2 := nat_to_bits_fold val
    refine And.intro v ?_
    calc
      Str2Int (bits_to_string (nat_to_bits val)) = (nat_to_bits val).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := eq1
      _ = val := eq2
-- </vc-proof>

end BignumLean