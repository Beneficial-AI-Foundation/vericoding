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

// <vc-helpers>
function Str2Int(s: string): nat
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

function Int2StrRecursive(n: nat, acc: string): string
{
  if n == 0 then acc
  else Int2StrRecursive(n / 2, acc + (if n % 2 == 0 then "0" else "1"))
}

function Reverse(s: string): string
{
  if |s| <= 1 then s else [s[|s|-1]] + Reverse(s[0..|s|-1])
}

function Int2Str(n: nat): string
{
  if n == 0 then "0"
  else Reverse(Int2StrRecursive(n, ""))
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
  var d := Str2Int(dividend);
  var dv := Str2Int(divisor);
  quotient := Int2Str(d / dv);
  remainder := Int2Str(d % dv);
}
// </vc-code>

