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
function method BitsToNat(s: string): nat
  requires ValidBitString(s)
  ensures result == Str2Int(s)
  decreases s
{
  var res := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant 0 <= res
    invariant res == Str2Int(s[0..i])
  {
    res := 2 * res + (if s[i] == '1' then 1 else 0);
    i := i + 1;
  }
  res
}

function method NatToBits(n: nat): string
  ensures ValidBitString(result) && Str2Int(result) == n
  decreases n
{
  if n == 0 then "0"
  else
    var rec := NatToBits(n / 2);
    var bit := if n % 2 == 1 then "1" else "0";
    if rec == "0" then bit else rec + bit
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
  var dv := BitsToNat(dividend);
  var ds := BitsToNat(divisor);
  var q := dv / ds;
  var r := dv % ds;
  quotient := NatToBits(q);
  remainder := NatToBits(r);
}
// </vc-code>

