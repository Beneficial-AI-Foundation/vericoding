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
lemma SameLengthNormalizedComparison(s1: string, s2: string, cmp: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| && |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 1 ==> s2[0] != '0'
  requires cmp == LexCompare(s1, s2)
  ensures cmp < 0 ==> Str2Int(s1) < Str2Int(s2)
  ensures cmp == 0 ==> Str2Int(s1) == Str2Int(s2)
  ensures cmp > 0 ==> Str2Int(s1) > Str2Int(s2)
{
  // This lemma states that for normalized bit strings of the same length,
  // lexicographic comparison corresponds to numeric comparison
}

function LexCompare(s1: string, s2: string): int
  ensures s1 == s2 ==> LexCompare(s1, s2) == 0
  ensures |s1| == |s2| && s1 != s2 ==> LexCompare(s1, s2) != 0
{
  if |s1| == 0 && |s2| == 0 then 0
  else if |s1| == 0 then -1
  else if |s2| == 0 then 1
  else if s1[0] < s2[0] then -1
  else if s1[0] > s2[0] then 1
  else LexCompare(s1[1..], s2[1..])
}

lemma LongerNormalizedIsGreater(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
  ensures Str2Int(s1) > Str2Int(s2)
{
  // For normalized bit strings, a longer string always represents a larger number
}
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
{
  var t1 := NormalizeBitString(s1);
  var t2 := NormalizeBitString(s2);
  
  if |t1| > |t2| {
    LongerNormalizedIsGreater(t1, t2);
    res := 1;
  } else if |t1| < |t2| {
    LongerNormalizedIsGreater(t2, t1);
    res := -1;
  } else {
    var cmp := LexCompare(t1, t2);
    SameLengthNormalizedComparison(t1, t2, cmp);
    if cmp < 0 {
      res := -1;
    } else if cmp == 0 {
      res := 0;
    } else {
      res := 1;
    }
  }
}
// </vc-code>

