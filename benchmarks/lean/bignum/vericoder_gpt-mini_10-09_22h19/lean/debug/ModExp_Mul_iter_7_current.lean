namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin : Nat → String
| 0 => "0"
| n+1 =>
  let m := n+1
  let q := m / 2
  let bit := if m % 2 = 1 then '1' else '0'
  if q = 0 then String.singleton bit else (nat_to_bin q).push bit
termination_by _ => n
decreasing_by
  dsimp
  have : 2 > 1 := by decide
  apply Nat.div_lt_self (n+1) 2 this

-- LLM HELPER
theorem Str2Int_push_char (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- unfold the push on underlying array and use the definition of Array.foldl on push
  have : (s.push c).data = s.data.push c := rfl
  rw [this]
  -- By definition of Array.foldl, folding over arr.push x equals f (arr.foldl f init) x;
  -- this reduces definitionally
  rfl

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ n, ValidBitString (nat_to_bin n) ∧ Str2Int (nat_to_bin n) = n := by
  apply Nat.strongInductionOn
  intro m IH
  cases m
  · -- m = 0
    dsimp [nat_to_bin]
    constructor
    · intro i c h
      -- nat_to_bin 0 = "0", only index 0 yields some char '0'
      have : nat_to_bin 0 = "0" := rfl
      rw [this] at h
      -- analyze index
      cases i
      · -- i = 0
        dsimp [String.get?] at h
        injection h with heq
        subst heq
        left; rfl
      · -- i > 0 so get? = none, contradiction
        dsimp [String.get?] at h
        contradiction
    · -- Str2Int "0" = 0 by computation
      dsimp [Str2Int]; rfl
  · -- m = n+1 case
    let k := m
    dsimp [nat_to_bin]
    let q := k / 2
    let bit := if k % 2 = 1 then '1' else '0'
    have Hdef : nat_to_bin k = if q = 0 then String.singleton bit else (nat_to_bin q).push bit := rfl
    rw [Hdef]
    by_cases hq : q = 0
    · -- q = 0, so nat_to_bin k = singleton bit
      simp [hq]
      constructor
      · intro i c h
        -- only index 0 can return a char
        rw [String.get?_singleton] at h
        cases h with i_eq c_eq
        injection c_eq with cval
        subst cval
        -- bit was chosen from k%2, so it's '0' or '1'
        cases (k % 2 = 1)
        · simp [bit]; left; rfl
        · simp [bit]; left; rfl
      · -- Str2Int of singleton equals (if bit='1' then 1 else 0), and since q=0 we have k
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_to_bin : Nat → String
| 0 => "0"
| n+1 =>
  let m := n+1
  let q := m / 2
  let bit := if m % 2 = 1 then '1' else '0'
  if q = 0 then String.singleton bit else (nat_to_bin q).push bit
termination_by _ => n
decreasing_by
  dsimp
  have : 2 > 1 := by decide
  apply Nat.div_lt_self (n+1) 2 this

-- LLM HELPER
theorem Str2Int_push_char (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- unfold the push on underlying array and use the definition of Array.foldl on push
  have : (s.push c).data = s.data.push c := rfl
  rw [this]
  -- By definition of Array.foldl, folding over arr.push x equals f (arr.foldl f init) x;
  -- this reduces definitionally
  rfl

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ n, ValidBitString (nat_to_bin n) ∧ Str2Int (nat_to_bin n) = n := by
  apply Nat.strongInductionOn
  intro m IH
  cases m
  · -- m = 0
    dsimp [nat_to_bin]
    constructor
    · intro i c h
      -- nat_to_bin 0 = "0", only index 0 yields some char '0'
      have : nat_to_bin 0 = "0" := rfl
      rw [this] at h
      -- analyze index
      cases i
      · -- i = 0
        dsimp [String.get?] at h
        injection h with heq
        subst heq
        left; rfl
      · -- i > 0 so get? = none, contradiction
        dsimp [String.get?] at h
        contradiction
    · -- Str2Int "0" = 0 by computation
      dsimp [Str2Int]; rfl
  · -- m = n+1 case
    let k := m
    dsimp [nat_to_bin]
    let q := k / 2
    let bit := if k % 2 = 1 then '1' else '0'
    have Hdef : nat_to_bin k = if q = 0 then String.singleton bit else (nat_to_bin q).push bit := rfl
    rw [Hdef]
    by_cases hq : q = 0
    · -- q = 0, so nat_to_bin k = singleton bit
      simp [hq]
      constructor
      · intro i c h
        -- only index 0 can return a char
        rw [String.get?_singleton] at h
        cases h with i_eq c_eq
        injection c_eq with cval
        subst cval
        -- bit was chosen from k%2, so it's '0' or '1'
        cases (k % 2 = 1)
        · simp [bit]; left; rfl
        · simp [bit]; left; rfl
      · -- Str2Int of singleton equals (if bit='1' then 1 else 0), and since q=0 we have k
-- </vc-code>

end BignumLean