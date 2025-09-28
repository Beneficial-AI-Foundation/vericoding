// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
ghost function Power(b: nat, e: nat): nat
{
  if e == 0 then 1 else b * Power(b, e - 1)
}

lemma Power2Times(e: nat)
  ensures 2 * Power(2, e) == Power(2, e + 1)
{
}

lemma Power2Monotonic(e1: nat, e2: nat)
  requires e1 >= e2
  ensures Power(2, e1) >= Power(2, e2)
  decreases e1 - e2
{
  if e1 > e2 {
    Power2Monotonic(e1 - 1, e2);
  }
}

lemma Str2IntUpperBound(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < Power(2, |s|)
  decreases |s|
{
  if |s| > 0 {
    var prefix := s[0..|s|-1];
    Str2IntUpperBound(prefix);
    Power2Times(|prefix|);
  }
}

lemma Str2IntLowerBound(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '1'
  ensures Str2Int(s) >= Power(2, |s|-1)
  decreases |s|
{
  if |s| > 1 {
    var prefix := s[0..|s|-1];
    Str2IntLowerBound(prefix);
    Power2Times(|prefix| - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method CompareUnequal(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
// </vc-spec>
// <vc-code>
{
  // Given |s1| > |s2|, we know |s1| >= |s2| + 1. Since |s2| > 0, |s1| >= 2.
  // This engages the precondition `|s1| > 1 ==> s1[0] != '0'`, so s1[0] is '1'.
  // These facts satisfy the preconditions for the helper lemmas.
  Str2IntLowerBound(s1);
  Str2IntUpperBound(s2);
  Power2Monotonic(|s1|-1, |s2|);

  // The lemmas establish: Str2Int(s1) >= Power(2, |s1|-1) >= Power(2, |s2|) > Str2Int(s2).
  // Therefore Str2Int(s1) > Str2Int(s2) is always true.
  res := 1;
}
// </vc-code>
