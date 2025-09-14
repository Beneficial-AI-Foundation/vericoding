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
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

lemma Str2IntSuffixLemma(s: string, n: nat)
  requires ValidBitString(s)
  requires n <= |s|
  ensures Str2Int(s) == Str2Int(s[..n]) * pow2(|s| - n) + Str2Int(s[n..])
  decreases |s| - n
{
  if n == |s| {
    assert s[n..] == "";
    assert Str2Int(s[n..]) == 0;
  } else if n < |s| {
    Str2IntSuffixLemma(s, n + 1);
    calc {
      Str2Int(s);
      ==
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { Str2IntSuffixLemma(s[0..|s|-1], n); }
      2 * (Str2Int(s[0..|s|-1][..n]) * pow2(|s|-1 - n) + Str2Int(s[0..|s|-1][n..])) + (if s[|s|-1] == '1' then 1 else 0);
      == { assert s[0..|s|-1][..n] == s[..n]; assert s[0..|s|-1][n..] == s[n..|s|-1]; }
      2 * (Str2Int(s[..n]) * pow2(|s|-1 - n) + Str2Int(s[n..|s|-1])) + (if s[|s|-1] == '1' then 1 else 0);
      ==
      Str2Int(s[..n]) * (2 * pow2(|s|-1 - n)) + (2 * Str2Int(s[n..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
      == { assert 2 * pow2(|s|-1 - n) == pow2(|s| - n); }
      Str2Int(s[..n]) * pow2(|s| - n) + (2 * Str2Int(s[n..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
      == { assert s[n..] == s[n..|s|-1] + [s[|s|-1]]; }
      Str2Int(s[..n]) * pow2(|s| - n) + Str2Int(s[n..]);
    }
  }
}

function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma Pow2Positive(n: nat)
  ensures pow2(n) > 0
{
  if n > 0 {
    Pow2Positive(n - 1);
  }
}

function AddBitStrings(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(AddBitStrings(s1, s2))
  ensures Str2Int(AddBitStrings(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else {
    var last1 := s1[|s1|-1];
    var last2 := s2[|s2|-1];
    var sum := (if last1 == '1' then 1 else 0) + (if last2 == '1' then 1 else 0);
    var carry := sum / 2;
    var digit := sum % 2;
    var prefix := AddBitStrings(s1[..|s1|-1], s2[..|s2|-1]);
    if carry > 0 then
      AddBitStrings(prefix, "1") + (if digit == 1 then "1" else "0")
    else
      prefix + (if digit == 1 then "1" else "0")
  }
}

function MultiplyBitStrings(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(MultiplyBitStrings(s1, s2))
  ensures Str2Int(MultiplyBitStrings(s1, s2)) == Str2Int(s1) * Str2Int(s2)
{
  if |s2| == 0 then "0"
  else {
    var last := s2[|s2|-1];
    var rest := MultiplyBitStrings(s1, s2[..|s2|-1]);
    if last == '1' then
      AddBitStrings(rest + "0", s1)
    else
      rest + "0"
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
  quotient := "0";
  remainder := dividend;

  while (|remainder| > 0 && Str2Int(remainder) >= Str2Int(divisor))
    invariant ValidBitString(quotient) && ValidBitString(remainder)
    invariant Str2Int(dividend) == Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder)
    invariant Str2Int(remainder) < Str2Int(divisor) * pow2(|remainder|)
    decreases Str2Int(remainder)
  {
    var n := |remainder|;
    var partialDividend := remainder;
    var partialQuotient := "0";
    
    while (|partialDividend| > 0 && Str2Int(partialDividend) >= Str2Int(divisor))
      invariant ValidBitString(partialDividend) && ValidBitString(partialQuotient)
      invariant Str2Int(remainder) == Str2Int(partialQuotient) * Str2Int(divisor) + Str2Int(partialDividend)
      invariant |partialDividend| <= n
      decreases Str2Int(partialDividend)
    {
      var newPartial := partialDividend[1..];
      var newQuotient := partialQuotient + "1";
      
      if (Str2Int(newPartial) >= Str2Int(divisor)) {
        partialDividend := newPartial;
        partialQuotient := newQuotient;
      } else {
        partialDividend := "0" + newPartial;
        if |newQuotient| > 1 then
          partialQuotient := newQuotient[..|newQuotient|-1] + "0"
        else
          partialQuotient := "0";
      }
    }
    
    remainder := partialDividend;
    quotient := quotient + partialQuotient;
  }
}
// </vc-code>

