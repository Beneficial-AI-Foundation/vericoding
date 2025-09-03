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
method ParseString(s: string) returns (res: nat)
  requires ValidBitString(s)
  ensures res == Str2Int(s)
{
  var acc: nat := 0;
  var i: nat := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant acc == Str2Int(s[0..i])
    decreases |s| - i
  {
    var bit: nat := if s[i] == '1' then 1 else 0;
    acc := 2 * acc + bit;
    i := i + 1;
  }
  res := acc;
}

method IntToBin(m: nat) returns (res: string)
  ensures ValidBitString(res)
  ensures Str2Int(res) == m
{
  if m == 0 {
    res := "0";
    return;
  }
  var n := m;
  res := "";
  var pow: nat := 1; // pow = 2^{|res|}
  // invariant: m == Str2Int(res) + n * pow
  while n > 0
    invariant n >= 0
    invariant pow >= 1
    invariant ValidBitString(res)
    invariant m == Str2Int(res) + n * pow
    decreases n
  {
    var bit := n % 2;
    n := n / 2;
    var ch := if bit == 1 then "1" else "0";
    res := ch + res;
    pow := pow * 2;
  }
  // now n == 0, so m == Str2Int(res)
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
  var n := ParseString(dividend);
  var d := ParseString(divisor);
  var q := n / d;
  var r := n % d;
  quotient := IntToBin(q);
  remainder := IntToBin(r);
}
// </vc-code>

