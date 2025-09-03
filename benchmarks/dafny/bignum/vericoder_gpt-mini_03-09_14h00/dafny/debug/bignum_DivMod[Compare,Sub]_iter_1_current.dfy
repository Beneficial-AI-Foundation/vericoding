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

method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
method ToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    n := 0;
    return;
  }
  var prefix := s[0..|s|-1];
  var bit := if s[|s|-1] == '1' then 1 else 0;
  var np := ToNat(prefix);
  n := 2 * np + bit;
}

method IntToStr(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
    return;
  }
  var q := n / 2;
  var r := n % 2;
  var qs := IntToStr(q);
  var ch := if r == 1 then "1" else "0";
  s := qs + ch;
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
  var n := ToNat(dividend);
  var d := ToNat(divisor);
  var qn := n / d;
  var rn := n % d;
  quotient := IntToStr(qn);
  remainder := IntToStr(rn);
}
// </vc-code>

