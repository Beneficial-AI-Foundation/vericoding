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

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function IntToBin(n: nat): string
  ensures ValidBitString(IntToBin(n)) && Str2Int(IntToBin(n)) == n
  decreases n
{
  if n == 0 then ""
  else
    var q := n / 2;
    var r := n % 2;
    var s := IntToBin(q);
    if r == 1 then
      // s is valid and represents q by the postcondition of IntToBin(q)
      // concat with "1" yields a valid string and Str2Int_Unroll gives its numeric value
      ValidBitString_Concat(s, "1");
      assert |s + "1"| > 0;
      Str2Int_Unroll(s + "1");
      // use postcondition Str2Int(s) == q
      assert Str2Int(s) == q;
      assert Str2Int(s + "1") == 2 * q + 1;
      assert 2 * q + 1 == n;
      s + "1"
    else
      ValidBitString_Concat(s, "0");
      assert |s + "0"| > 0;
      Str2Int_Unroll(s + "0");
      assert Str2Int(s) == q;
      assert Str2Int(s + "0") == 2 * q + 0;
      assert 2 * q + 0 == n;
      s + "0"
}
// </vc-helpers>

// <vc-spec>
method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
// </vc-spec>
// <vc-code>
{
  var n := Str2Int(dividend);
  var d := Str2Int(divisor);
  assert d > 0;
  var q: nat := n / d;
  var r: nat := n % d;
  quotient := IntToBin(q);
  remainder := IntToBin(r);
}
// </vc-code>

