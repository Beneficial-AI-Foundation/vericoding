namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

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

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def bits_rev : Nat -> List Char
| 0     => []
| n+1   =>
  let r := (n+1) % 2
  let k := (n+1) / 2
  let ch := if r = 1 then '1' else '0'
  ch :: bits_rev k

-- LLM HELPER
def nat_to_bin (n : Nat) : String :=
  String.mk (List.reverse (bits_rev n))

-- LLM HELPER
theorem foldl_append_single {α β : Type} (f : β → α → β) :
    ∀ (l : List α) (init : β) (x : α),
      (List.foldl f init (l ++ [x])) = f (List.foldl f init l) x := by
  intro l
  induction l with
  | nil =>
    intro init x
    simp [List.foldl]
  | cons hd tl ih =>
    intro init x
    simp [List.foldl]
    calc
      List.foldl f init (hd :: tl ++ [x]) = List.foldl f (f init hd) (tl ++ [x]) := by rfl
      _ = f (List.foldl f (f init hd) tl) x := by
        apply ih
      _ = f (List.foldl f init (hd :: tl)) x := by
        simp [List.foldl]

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ (n : Nat),
  (nat_to_bin n).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  intro n
  apply Nat.strongRecOn n
  intro m IH
  cases m with
  | zero =>
    simp [nat_to_bin, bits_rev, List.reverse, List.foldl]
  | succ m' =>
    let t := m
    let k := t / 2
    let r := t % 2
    have h_bits : bits_rev t = (if r = 1 then '1' else '0') :: bits_rev k := by
      simp [bits_rev]
    dsimp [nat_to_bin]
    rw [h_bits]
    rw [List.reverse_cons]
    let f := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
    have happ := foldl_append_single f (List.reverse (bits_rev k)) 0 (if r = 1 then '1' else '0')
    rw [happ]
    have hk : k < t := by
      apply Nat.div_lt_self t (by norm_num : 2 > 1)
    have ihk := IH k hk
    have data_eq : (nat_to_bin k).data = List.reverse (bits_rev k) := by
      simp [nat_to_bin]
    rw [←data_eq] at ihk
    rw [ihk]
    have char_bit : (if (if r = 1 then '1' else '0') = '1' then 1 else 0) = r := by
      cases r
      · simp
      · simp
    rw [char_bit]
    have hdiv := Nat.div_add_mod t 2
    simp [hdiv]
    rfl

-- LLM HELPER
theorem list_get?_mem {α : Type} : ∀ {l : List α} {i : Nat} {a : α}, l.get? i = some a → a ∈ l := by
  intros l
  induction l with
  | nil =>
    intros i a h
    simp [List.get?] at h
    contradiction
  | cons hd tl ih =>
    intros i a h
    cases i
    · simp [List.get?] at h
      injection h with h'; subst h'; left; rfl
    · simp [List.get?] at h
      right
      apply ih
      exact h

-- LLM HELPER
theorem ValidBitString_nat_to_bin : ∀ (n : Nat), ValidBitString (nat_to_bin n) := by
  intro n
  unfold ValidBitString
  intro i c h
  -- reduce nat_to_bin and relate String.get? to list.get? on the underlying data
  dsimp [nat_to_bin] at h
  -- (String.mk l).get? i reduces to l.get? i.1 where i.1 is the underlying Nat index
  have : (List.reverse (bits_rev n)).get? i.1 = some c := by
    exact h
  have hmem := list_get?_mem this
  have mem_rev := (List.mem_reverse _ _).mp hmem
  have bits_prop : ∀ ch, ch ∈ bits_rev n → (ch = '0' ∨ ch = '1') := by
    intro ch hin
    induction n with
    | zero =>
      simp at hin
      contradiction
    | succ n ih =>
      simp [bits_rev] at hin
      cases hin with
      | head =>
        let r := (n+1) % 2
        by_cases hr : r = 1
        · simp [hr]; left; rfl
        · simp [hr]; right; rfl
      | tail =>
        apply ih
        assumption
  exact bits_prop c mem_rev
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  nat_to_bin (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
simp [ModExp, nat_to_bin]
constructor
· apply ValidBitString_nat_to_bin
· apply Str2Int_nat_to_bin
-- </vc-proof>

end BignumLean