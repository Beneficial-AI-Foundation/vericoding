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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Exp_int_impl(x: nat, y: nat): nat
{
  if y == 0 then 1 else x * Exp_int_impl(x, y - 1)
}

function Str2Int_impl(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2Int_impl(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then "0"
  else Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

method Add_impl(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var a := Str2Int_impl(s1);
  var b := Str2Int_impl(s2);
  var sum := a + b;
  res := Int2Str(sum);
}

method DivMod_impl(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var dvd := Str2Int_impl(dividend);
  var dvs := Str2Int_impl(divisor);
  quotient := Int2Str(dvd / dvs);
  remainder := Int2Str(dvd % dvs);
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var sum := "0";
  var len1 := |s1|;
  var idx := 0;
  while (idx < len1)
    invariant ValidBitString(sum)
    invariant Str2Int(sum) == Str2Int(s1[..idx]) * Str2Int(s2)
  {
    var append_count := len1 - 1 - idx;
    if s1[idx] == '1' {
      var shifted_s2 := s2;
      for i := 1 to append_count
        invariant ValidBitString(shifted_s2)
      { shifted_s2 := shifted_s2 + "0"; }
      sum := Add_impl(sum, shifted_s2);
    }
    idx := idx + 1;
  }
  res := sum;
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
    if sy == "0" {
      res := "1";
    } else {
      var _, rem := DivMod_impl(sx, sz);
      res := rem;
    }
  } else {
    var res' := ModExpPow2(sx, sy[0..|sy|-1], n - 1, sz);
    var square := Mul(res', res');
    var _, rem := DivMod_impl(square, sz);
    res := rem;
  }
}
// </vc-code>

