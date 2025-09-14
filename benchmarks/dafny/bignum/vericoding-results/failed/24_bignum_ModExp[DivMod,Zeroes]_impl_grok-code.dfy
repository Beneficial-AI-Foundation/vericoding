ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Str2Int_method(s: string): nat
  requires ValidBitString(s)
  ensures Str2Int_method(s) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 then 0 else if s[0] == '0' then Str2Int_method(s[1..]) else Exp_int(2, |s|-1) + Str2Int_method(s[1..])
}

method Nat2BitString(n: nat) returns (result: string)
  ensures ValidBitString(result)
  ensures Str2Int(result) == n
  ensures n == 0 ==> |result| == 1 && result == "0"
  ensures n > 0 ==> |result| > 0 && result[0] == '1'
  decreases n
{
  result := "";
  var nn := n;
  while nn > 0
    decreases nn
  {
    result := (if nn % 2 == 1 then "1" else "0") + result;
    nn := nn / 2;
  }
  if result == "" {
    result := "0";
  }
}

method ComputeModExp(x: nat, y: nat, z: nat) returns (r: nat)
  requires z > 1
  ensures r == Exp_int(x, y) % z
{
  r := 1;
  var i := 0;
  while i <= y
    invariant i <= y && r == Exp_int(x, i) % z
    decreases y - i
  {
    if i < y {
      r := (r * x) % z;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  var x_nat := Str2Int_method(sx);
  var y_nat := Str2Int_method(sy);
  var z_nat := Str2Int_method(sz);
  var res_nat := ComputeModExp(x_nat, y_nat, z_nat);
  res := Nat2BitString(res_nat);
}
// </vc-code>

