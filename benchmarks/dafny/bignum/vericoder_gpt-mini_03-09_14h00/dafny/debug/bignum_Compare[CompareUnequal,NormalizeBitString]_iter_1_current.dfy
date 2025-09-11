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

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

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
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function twoPow(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * twoPow(n - 1)
}

lemma Str2Int_lt_twoPow(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < twoPow(|s|)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var pref := s[0..|s|-1];
    Str2Int_lt_twoPow(pref);
    // Str2Int(s) = 2*Str2Int(pref) + bit, and by IH Str2Int(pref) < twoPow(|pref|)
    // so Str2Int(s) < 2*twoPow(|pref|) = twoPow(|s|)
  }
}

lemma Str2Int_ge_twoPow_if_leading1(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '1'
  ensures Str2Int(s) >= twoPow(|s| - 1)
  decreases |s|
{
  if |s| == 1 {
    // s == "1"
  } else {
    var pref := s[0..|s|-1];
    // pref also has leading '1'
    Str2Int_ge_twoPow_if_leading1(pref);
    // Str2Int(s) = 2*Str2Int(pref) + bit >= 2 * twoPow(|pref|-1) = twoPow(|s|-1)
  }
}

lemma twoPow_monotone(n1: nat, n2: nat)
  requires n1 >= n2
  ensures twoPow(n1) >= twoPow(n2)
  decreases n1 - n2
{
  if n1 == n2 {
  } else {
    twoPow_monotone(n1 - 1, n2);
    // twoPow(n1) = 2 * twoPow(n1-1) >= 2 * twoPow(n2) >= twoPow(n2)
  }
}

lemma RemoveLeadingZero(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..|s|])
  decreases |s|
{
  if |s| == 1 {
    // both sides are 0
  } else {
    // s = '0' + rest
    var pref := s[0..|s|-1]; // prefix including the leading 0 and excluding last char
    // pref[0] == '0', so we can apply IH to pref
    RemoveLeadingZero(pref);
    // Str2Int(s) = 2 * Str2Int(pref) + lastbit
    // Str2Int(s[1..]) = 2 * Str2Int(pref[1..]) + lastbit
    // By IH Str2Int(pref) == Str2Int(pref[1..]), hence equality
  }
}

lemma RemoveLeadingZeros(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < i ==> s[j] == '0'
  ensures Str2Int(s) == Str2Int(s[i..|s|])
  decreases i
{
  if i == 0 {
  } else {
    // s[0] == '0'
    RemoveLeadingZero(s);
    // Str2Int(s) == Str2Int(s[1..])
    // Now apply IH to s[1..] with i-1
    var s1 := s[1..|s|];
    // For j < i-1, s1[j] = s[j+1] == '0'
    RemoveLeadingZeros(s1, i - 1);
  }
}

lemma Str2IntConcat(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == Str2Int(a) * twoPow(|b|) + Str2
// </vc-helpers>

// <vc-spec>
method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
ghost function twoPow(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * twoPow(n - 1)
}

lemma Str2Int_lt_twoPow(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < twoPow(|s|)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var pref := s[0..|s|-1];
    Str2Int_lt_twoPow(pref);
    // Str2Int(s) = 2*Str2Int(pref) + bit, and by IH Str2Int(pref) < twoPow(|pref|)
    // so Str2Int(s) < 2*twoPow(|pref|) = twoPow(|s|)
  }
}

lemma Str2Int_ge_twoPow_if_leading1(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '1'
  ensures Str2Int(s) >= twoPow(|s| - 1)
  decreases |s|
{
  if |s| == 1 {
    // s == "1"
  } else {
    var pref := s[0..|s|-1];
    // pref also has leading '1'
    Str2Int_ge_twoPow_if_leading1(pref);
    // Str2Int(s) = 2*Str2Int(pref) + bit >= 2 * twoPow(|pref|-1) = twoPow(|s|-1)
  }
}

lemma twoPow_monotone(n1: nat, n2: nat)
  requires n1 >= n2
  ensures twoPow(n1) >= twoPow(n2)
  decreases n1 - n2
{
  if n1 == n2 {
  } else {
    twoPow_monotone(n1 - 1, n2);
    // twoPow(n1) = 2 * twoPow(n1-1) >= 2 * twoPow(n2) >= twoPow(n2)
  }
}

lemma RemoveLeadingZero(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..|s|])
  decreases |s|
{
  if |s| == 1 {
    // both sides are 0
  } else {
    // s = '0' + rest
    var pref := s[0..|s|-1]; // prefix including the leading 0 and excluding last char
    // pref[0] == '0', so we can apply IH to pref
    RemoveLeadingZero(pref);
    // Str2Int(s) = 2 * Str2Int(pref) + lastbit
    // Str2Int(s[1..]) = 2 * Str2Int(pref[1..]) + lastbit
    // By IH Str2Int(pref) == Str2Int(pref[1..]), hence equality
  }
}

lemma RemoveLeadingZeros(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < i ==> s[j] == '0'
  ensures Str2Int(s) == Str2Int(s[i..|s|])
  decreases i
{
  if i == 0 {
  } else {
    // s[0] == '0'
    RemoveLeadingZero(s);
    // Str2Int(s) == Str2Int(s[1..])
    // Now apply IH to s[1..] with i-1
    var s1 := s[1..|s|];
    // For j < i-1, s1[j] = s[j+1] == '0'
    RemoveLeadingZeros(s1, i - 1);
  }
}

lemma Str2IntConcat(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == Str2Int(a) * twoPow(|b|) + Str2
// </vc-code>

