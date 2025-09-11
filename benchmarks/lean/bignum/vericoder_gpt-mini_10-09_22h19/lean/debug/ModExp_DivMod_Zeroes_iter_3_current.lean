namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def natToBinList : Nat -> List Char
| 0     => ['0']
| (n+1) =>
  let k := n+1
  if k = 1 then
    ['1']
  else
    natToBinList (k / 2) ++ [if k % 2 = 1 then '1' else '0']

-- LLM HELPER
def natToString (n : Nat) : String :=
  String.mk (natToBinList n)

-- LLM HELPER
theorem Str2Int_append_char (l : List Char) (c : Char) :
  Str2Int (String.mk (l ++ [c])) = 2 * Str2Int (String.mk l) + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int, natToString]
  -- foldl on appended list: foldl f acc (l ++ [c]) = foldl f acc l then process [c]
  rw [List.foldl_append]
  -- compute foldl on singleton [c]
  simp [List.foldl]
  rfl

-- LLM HELPER
theorem List_get?_mem {α : Type} :
  ∀ {l : List α} {n : Nat} {x : α}, l.get? n = some x → x ∈ l := by
  intros l
  induction l with
  | nil =>
    intros n x h
    cases h
  | cons hd tl ih =>
    intros n x h
    cases n with
    | zero =>
      -- get? (hd :: tl) 0 = some hd
      simp [List.get?] at h
      injection h with h1
      subst h1
      apply List.mem_cons_self
    | succ n' =>
      simp [List.get?] at h
      have : tl.get? n' = some x := h
      apply List.mem_cons_of_mem hd
      apply ih this

-- LLM HELPER
theorem natToBinList_chars (n : Nat) :
  ∀ {a}, a ∈ natToBinList n → (a = '0' ∨ a = '1') := by
  induction n using Nat.strong_induction_on with n IH
  intro a h
  cases n
  · -- natToBinList 0 = ['0']
    dsimp [natToBinList] at h
    simp at h
    cases h
    · left; rfl
    · cases h
  cases n
  · -- natToBinList 1 = ['1']
    dsimp [natToBinList] at h
    simp at h
    cases h
    · right; rfl
    · cases h
  -- n >= 2
  let k := n
  dsimp [natToBinList] at *
  have hk : ¬(k = 1) := by intros he; linarith
  simp [hk] at h
  -- natToBinList k = natToBinList (k/2) ++ [bit]
  apply List.mem_append.1 h; cases ‹_› with
  | inl hin =>
    have hlt : k / 2 < k := by
      have : 1 < k := by linarith
      exact Nat.div_lt_self this
    exact (IH (k / 2) hlt _ hin)
  | inr hin =>
    simp at hin
    cases hin; subst hin
    simp
    right; dsimp
    -- bit is either '0' or '1' by construction
    cases (k % 2) <; simp_all

-- LLM HELPER
theorem String_mk_get?_eq (l : List Char) (i : String.Pos) :
  (String.mk l).get? i = l.get? i.toNat := by
  -- String.get? for a String.mk delegates to list.get? on the underlying data at i.toNat
  -- This unfolds by definition.
  -- We proceed by cases on i to expose its .toNat and then simplify.
  cases i
  -- now i.toNat is available as i
  dsimp [String.mk, String.get?]
  -- The definitions reduce to the corresponding list.get?
  -- Lean's simplifier will handle the concrete reduction.
  -- Use rfl as the definitions align.
  rfl

-- LLM HELPER
theorem Str2Int_natToString (n : Nat) : Str2Int (natToString n) = n := by
  induction n using Nat.strong_induction_on with n IH
  cases n
  · -- n = 0
    dsimp [natToString, natToBinList, Str2Int]
    simp
  cases n
  · -- n = 1
    dsimp [natToString, natToBinList, Str2Int]
    simp
  -- n >= 2
  let k := n
  dsimp [natToString]
  have hlist : natToBinList k = natToBinList (k / 2) ++ [if k % 2 = 1 then '1' else '0'] := by
    dsimp [natToBinList]
    have hk : ¬(k = 1) := by intros he; linarith
    simp [hk]
  rw [hlist]
  -- use append character lemma
  have H := Str2Int_append_char (natToBinList (k / 2)) (if k % 2 = 1 then '1' else '0')
  rw [H]
  -- induction hypothesis on k/2
  have hlt : k / 2 < k := by
    have : 1 < k := by linarith
    exact Nat.div_lt_self this
  have ih := IH (k / 2) hlt
  rw [←ih]
  -- reduce the final bit to numeric k % 2
  have bit_eq : (if (if k % 2 = 1 then '1' else '0') = '1' then 1 else 0) = (k % 2) := by
    dsimp
    cases (k % 2) <; simp_all
  simp [bit_eq]
  -- 2 * (k / 2) + k % 2 = k
  rw [Nat.div_mul_add_mod]
  rfl

-- LLM HELPER
theorem ValidBitString_natToString (n : Nat) : ValidBitString (natToString n) := by
  -- Show: for any position i and character c, if natToString n .get? i = some c then c is '0' or '1'.
  intro i c h
  -- relate string.get? to underlying list.get?
  have hlist : (natToBinList n).get? i.toNat = some c := by
    -- use the lemma relating String.mk and list.get?
    rw [←String_mk_get?_eq (natToBinList n) i] at h
    exact h
  -- from list.get? = some c obtain c ∈ natToBinList n
  have mem := List_get?_mem (hlist)
  -- then use natToBinList_chars to deduce it's '0' or '1'
  exact natToBinList_chars n mem
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute the numeric modular exponent, then convert to a binary string
  natToString (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  simp [ModExp]
  let r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
-- </vc-theorem>
end BignumLean