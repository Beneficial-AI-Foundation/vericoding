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
function Str2NatExec(s: string): nat
  requires ValidBitString(s)
  decreases s
  ensures Str2NatExec(s) == Str2Int(s)
{
  if |s| == 0 then
    0
  else
    2 * Str2NatExec(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function NatToBin(n: nat): string
  decreases n
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
{
  if n == 0 then
    ""
  else
    NatToBin(n / 2) + (if n % 2 == 1 then "1" else "0")
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
  var nDividend := Str2NatExec(dividend);
  var nDivisor := Str2NatExec(divisor);
  var q: nat := nDividend / nDivisor;
  var r: nat := nDividend % nDivisor;
  quotient := NatToBin(q);
  remainder := NatToBin(r);
}
// </vc-code>

