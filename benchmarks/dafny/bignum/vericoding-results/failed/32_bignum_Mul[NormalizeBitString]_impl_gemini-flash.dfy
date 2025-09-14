ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Multiply(s1: string, s2: string): nat
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Multiply(s1, s2) == Str2Int(s1) * Str2Int(s2)
{
  Str2Int(s1) * Str2Int(s2)
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then
    "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant n == Str2Int(s) + temp * Power(2, |s|)
      decreases temp
    {
      if temp % 2 == 1 then
        s := "1" + s;
      else
        s := "0" + s;
      temp := temp / 2;
    }
    s
}

function Power(base: nat, exp: nat): nat
  ensures Power(base, exp) == base as int power exp as int
  decreases exp
{
  if exp == 0 then
    1
  else
    base * Power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var product := n1 * n2;
  res := Int2Str(product);
}
// </vc-code>

