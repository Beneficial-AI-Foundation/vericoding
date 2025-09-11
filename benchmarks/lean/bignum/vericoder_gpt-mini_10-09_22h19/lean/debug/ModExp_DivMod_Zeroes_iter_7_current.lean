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
  dsimp [Str2Int]
  -- foldl over appended singleton
  rw [List.foldl_append]
  -- foldl over singleton [c]
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
  · -- n = 0
    dsimp [natToBinList] at h
    simp at h
    cases h
    · left; rfl
    · cases h
  cases n
  · -- n = 1
    dsimp [natToBinList] at h
    simp at h
    cases h
    · right; rfl
    · cases h
  -- n >= 2
  let k := n
  dsimp [natToBinList] at h
  have eq : natToBinList k = natToBinList (k / 2) ++ [if k % 2 = 1 then '1' else '0'] := by
    dsimp [natToBinList]
    have hk : k ≠ 1 := by
      intro he; linarith
    simp [hk]
  rw [eq] at h
  cases (List.mem_append.1 h) with
  | inl hin =>
    have hlt : k / 2 < k := by
      have : 1 < k := by linarith
      exact Nat.div_lt_self this
    exact IH (k / 2) hlt _ hin
  | inr hin =>
    simp at hin
    cases hin
    · subst hin
      by_cases hk : k % 2 = 1
      · left; simp [hk]
      · right; simp [hk]

-- LLM HELPER
theorem String_mk_get?_eq (l : List Char) (i : Nat) :
  (String.mk l).get? i = l.get? i := by
  -- String.get? on String.mk delegates to the underlying list.get?
  dsimp [String.mk, String.get?]
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
    have hk : ¬(k = 1) := by intro he; linarith
    simp [hk]
  rw [hlist]
  have H := Str2Int_append_char (natToBinList (k / 2)) (if k % 2 = 1 then '1' else '0')
  rw [H]
  have hlt : k / 2 < k := by
    have : 1 < k := by linarith
    exact Nat.div_lt_self this
  have ih := IH (k / 2) hlt
  rw [←ih]
  -- reduce final bit to numeric k % 2
  have bit_eq : (if (if k % 2 = 1 then '1' else '0') = '1' then 1 else 0) = (k % 2) := by
    by_cases hk : k % 2 = 1
    · simp [hk]
    · have : k % 2 = 0 := by
        have := Nat.mod_two_eq_zero_or_one k
        cases this with
        | inl h0 => exact h0
        | inr h1 => contradiction
      simp [this]
  simp [bit_eq]
  rw [Nat.div_mul_add_mod]
  rfl

-- LLM HELPER
theorem ValidBitString_natToString (n : Nat) : ValidBitString (natToString n) := by
  intro i c h
  have hlist : (natToBinList n).get? i = some c := by
    rw [←String_mk_get?_eq (natToBinList n) i] at h
    exact h
  have mem := List_get?_mem (hlist)
  exact natToBinList_chars n mem
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
natToString (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
simp [ModExp]
let r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
apply And.intro
· exact ValidBitString_natToString r
· exact (Str2Int_natToString r).symm
-- </vc-proof>

end BignumLean