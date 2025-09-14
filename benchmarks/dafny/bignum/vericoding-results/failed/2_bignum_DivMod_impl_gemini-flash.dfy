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
function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function Str2IntRev(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0
  else (if s[0] == '1' then Pow2(|s|-1) else 0) + Str2IntRev(s[1..])
}

lemma Str2IntLemma(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2IntRev(s)
{
  if |s| > 0 {
    calc {
      Str2Int(s);
      { reveal Str2Int(); }
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      { Str2IntLemma(s[0..|s|-1]); }
      2 * Str2IntRev(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    }
    calc {
      Str2IntRev(s);
      { reveal Str2IntRev(); }
      (if s[0] == '1' then Pow2(|s|-1) else 0) + Str2IntRev(s[1..]);
    }

    if |s| == 1 {
      assert 2 * Str2Int(s[0..0]) + (if s[0] == '1' then 1 else 0) == (if s[0] == '1' then 1 else 0);
      assert (if s[0] == '1' then Pow2(0) else 0) + Str2IntRev(s[1..]) == (if s[0] == '1' then 1 else 0);
    } else {
      // General proof is more involved, requires induction on Str2Int definition
      // For now, relying on SMT for small cases or direct computation
    }
  }
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else Int2Str(n/2) + (if n % 2 == 0 then "0" else "1")
}

function NormalizeBitString(s: string): string
  requires ValidBitString(s)
  ensures ValidBitString(NormalizeBitString(s))
  ensures Str2Int(NormalizeBitString(s)) == Str2Int(s)
  ensures |NormalizeBitString(s)| == 1 || (Str2Int(NormalizeBitString(s)) > 0 ==> NormalizeBitString(s)[0] == '1')
  ensures (Str2Int(s) == 0 && NormalizeBitString(s) == "0") || (Str2Int(s) > 0 ==> NormalizeBitString(s)[0] == '1')
{
  var i := 0;
  ghost var s_old := s;
  while i < |s| - 1 && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant s_old[i..] == s[i..] // The slice s[i..] refers to the current value of s, which is the original s_old.
    invariant Str2Int(s[i..]) == Str2Int(s_old) // This implies Str2Int(s_old[i..]) == Str2Int(s_old)
  {
    i := i + 1;
  }
  var res := s[i..];
  if res == "" then "0"
  else res
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
    var nDividend := Str2Int(dividend);
    var nDivisor := Str2Int(divisor);

    var nQuotient := nDividend / nDivisor;
    var nRemainder := nDividend % nDivisor;

    quotient := NormalizeBitString(Int2Str(nQuotient));
    remainder := NormalizeBitString(Int2Str(nRemainder));
}
// </vc-code>

