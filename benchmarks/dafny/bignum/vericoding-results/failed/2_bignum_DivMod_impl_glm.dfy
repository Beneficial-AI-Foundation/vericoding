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
function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then "0"
  else Int2StrHelper(n)
}

function Int2StrHelper(n: nat): string
  requires n > 0
  ensures ValidBitString(Int2StrHelper(n))
  ensures Str2Int(Int2StrHelper(n)) == n
  decreases n
{
  if n == 1 then "1"
  else 
    var rest := Int2StrHelper(n / 2);
    var bit := if n % 2 == 0 then "0" else "1";
    rest + bit
}

lemma Str2Int_properties(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
  ensures |s| == 0 ==> Str2Int(s) == 0
  ensures |s| > 0 ==> Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
  if |s| == 0 {
    calc {
      Str2Int(s);
      0;
    }
  } else {
    calc {
      Str2Int(s);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    }
  }
}

method ParseBitString(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
  {
    n := n * 2;
    if s[i] == '1' {
      n := n + 1;
    }
    i := i + 1;
  }
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
  var q := 0;
  var r := ParseBitString(dividend);
  var d := ParseBitString(divisor);
  
  while r >= d
    invariant 0 <= r
    invariant 0 <= q
    invariant Str2Int(dividend) == q * d + r
    decreases r
  {
    q := q + 1;
    r := r - d;
  }
  
  quotient := Int2Str(q);
  remainder := Int2Str(r);
}
// </vc-code>

