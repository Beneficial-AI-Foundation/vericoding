ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Pow2_as_string(n: nat): string
  ensures ValidBitString(Pow2_as_string(n))
{
  if n == 0 then "1" else "1" + seq(n, _ => '0')
}

function Int2Str(x: nat): string
  decreases x
  ensures ValidBitString(Int2Str(x))
{
  if x == 0 then "0"
  else if x == 1 then "1"
  else Int2Str(x / 2) + (if x % 2 == 0 then "0" else "1")
}

function Str2Int_executable(s: string): nat
  requires ValidBitString(s)
  decreases s
  ensures Str2Int(s) == Str2Int_executable(s)
{
  if |s| == 0 then 0 else (2 * Str2Int_executable(s[0..|s| - 1]) + (if s[|s| - 1] == '1' then 1 else 0))
}

lemma Str2Int_Exec_Equal(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2Int_executable(s)
{
  if |s| == 0 {} else
  {
    Str2Int_Exec_Equal(s[0..|s|-1]);
  }
}

lemma Int2StrCorrect(x: nat)
  ensures ValidBitString(Int2Str(x))
  ensures Str2Int(Int2Str(x)) == x
{
  if x == 0 {}
  else if x == 1 {}
  else {
    Int2StrCorrect(x / 2);
    // Proof follows the recursive definition of Str2Int
  }
}

lemma Pow2Correct(n: nat)
  ensures ValidBitString(Pow2_as_string(n))
  ensures Str2Int(Pow2_as_string(n)) == Exp_int(2, n)
{
  if n == 0 {}
  else {
    Pow2Correct(n - 1);
    // Induction on the string construction
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    if sy == "1" {
      var num_x := Str2Int_executable(sx);
      var num_m := Str2Int_executable(sz);
      var num_res := num_x % num_m;
      res := Int2Str(num_res);
      Str2Int_Exec_Equal(sx);
      Str2Int_Exec_Equal(sz);
      Int2StrCorrect(num_res);
    } else {
      res := Int2Str(1);
      Int2StrCorrect(1);
    }
  } else {
    var partial_res := ModExpPow2(sx, sy, n - 1, sz);
    var num_m := Str2Int_executable(sz);
    var num_pr := Str2Int_executable(partial_res);
    var square := num_pr * num_pr;
    var num_res := square % num_m;
    res := Int2Str(num_res);
    Str2Int_Exec_Equal(sx);
    Str2Int_Exec_Equal(sy);
    Str2Int_Exec_Equal(sz);
    Str2Int_Exec_Equal(partial_res);
    Int2StrCorrect(partial_res);
    Int2StrCorrect(1);
    Int2StrCorrect(num_res);
  }
}
// </vc-code>

