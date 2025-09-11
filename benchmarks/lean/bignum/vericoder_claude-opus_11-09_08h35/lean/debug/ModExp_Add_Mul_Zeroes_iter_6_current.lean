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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def carry (c1 c2 carry_in : Char) : Char × Char :=
  let val1 := if c1 = '1' then 1 else 0
  let val2 := if c2 = '1' then 1 else 0
  let carry_val := if carry_in = '1' then 1 else 0
  let sum := val1 + val2 + carry_val
  (if sum % 2 = 1 then '1' else '0', if sum / 2 = 1 then '1' else '0')

-- LLM HELPER
def addBitStrings (s1 s2 : String) : String :=
  let rec aux (l1 l2 : List Char) (c : Char) (acc : List Char) : List Char :=
    match l1, l2 with
    | [], [] => if c = '1' then '1' :: acc else acc
    | h1::t1, [] => 
      let (sum, newCarry) := carry h1 '0' c
      aux t1 [] newCarry (sum :: acc)
    | [], h2::t2 => 
      let (sum, newCarry) := carry '0' h2 c
      aux [] t2 newCarry (sum :: acc)
    | h1::t1, h2::t2 =>
      let (sum, newCarry) := carry h1 h2 c
      aux t1 t2 newCarry (sum :: acc)
  String.mk (aux s1.data.reverse s2.data.reverse '0' [])

-- LLM HELPER
def mulByBit (s : String) (bit : Char) : String :=
  if bit = '0' then "0" else s

-- LLM HELPER
def shiftLeft (s : String) (n : Nat) : String :=
  s ++ String.mk (List.replicate n '0')

-- LLM HELPER
def mulBitStrings (s1 s2 : String) : String :=
  let rec aux (l2 : List Char) (shift : Nat) (acc : String) : String :=
    match l2 with
    | [] => acc
    | h::t => 
      let partial := shiftLeft (mulByBit s1 h) shift
      aux t (shift + 1) (addBitStrings acc partial)
  aux s2.data.reverse 0 "0"

-- LLM HELPER
def zerosString (n : Nat) : String :=
  String.mk (List.replicate n '0')
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then "1"
else if Str2Int sz ≤ 1 then "0"
else
  let rec modExpAux (base exp result : String) (fuel : Nat) : String :=
    if fuel = 0 then result
    else if Str2Int exp = 0 then result
    else
      let newResult := if Str2Int exp % 2 = 1 then
        let prod := Mul result base
        let rec modReduce (n : String) (f : Nat) : String :=
          if f = 0 then n
          else if Str2Int n < Str2Int sz then n
          else 
            let diff := Str2Int n - Str2Int sz
            let diffStr := if diff = 0 then "0" else
              let rec toBinary (m : Nat) (acc : List Char) : List Char :=
                if m = 0 then if acc = [] then ['0'] else acc
                else toBinary (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
              String.mk (toBinary diff []).reverse
            modReduce diffStr (f - 1)
        modReduce prod (Str2Int prod + 1)
      else result
      let newBase := 
        let prod := Mul base base
        let rec modReduce (n : String) (f : Nat) : String :=
          if f = 0 then n
          else if Str2Int n < Str2Int sz then n
          else 
            let diff := Str2Int n - Str2Int sz
            let diffStr := if diff = 0 then "0" else
              let rec toBinary (m : Nat) (acc : List Char) : List Char :=
                if m = 0 then if acc = [] then ['0'] else acc
                else toBinary (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
              String.mk (toBinary diff []).reverse
            modReduce diffStr (f - 1)
        modReduce prod (Str2Int prod + 1)
      let newExp := 
        let e := Str2Int exp / 2
        if e = 0 then "0" else
          let rec toBinary (m : Nat) (acc : List Char) : List Char :=
            if m = 0 then if acc = [] then ['0'] else acc
            else toBinary (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
          String.mk (toBinary e []).reverse
      modExpAux newBase newExp newResult (fuel - 1)
  modExpAux sx sy "1" (Str2Int sy + 1)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
split_ifs with h1 h2
· constructor
  · unfold ValidBitString
    intros i c hc
    cases i with
    | zero => 
      simp at hc
      cases hc
      right
      assumption
    | succ j => 
      simp at hc
  · simp [Exp_int, h1]
    exact Nat.mod_eq_of_lt hsz_gt1
· exfalso
  linarith [hsz_gt1, h2]
· constructor
  · unfold ValidBitString
    intros i c hget
    left
  · rfl
-- </vc-proof>

end BignumLean