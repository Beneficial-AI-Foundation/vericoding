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
  var num_leading_zeros := 0;
  while num_leading_zeros < |s|-1 && s[num_leading_zeros] == '0'
    invariant 0 <= num_leading_zeros <= |s|
    invariant forall i | 0 <= i < num_leading_zeros :: s[i] == '0'
    decreases |s| - num_leading_zeros
  {
    num_leading_zeros := num_leading_zeros + 1;
  }
  t := s[num_leading_zeros..];
  if |t| == 0 { // Handle case where s was "0" or "000..."
      t := "0";
  }
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
  requires |s1| != |s2| // This is the crucial part that differentiates this from other compare methods
{
  if |s1| > |s2| {
    res := 1;
  } else if |s1| < |s2| {
    res := -1;
  } else {
    // This case should not be reached due to the `requires |s1| != |s2|` clause.
    // However, Dafny demands a return value for all paths.
    // In a real scenario, this would indicate an assertion failure or be unreachable.
    res := 0; 
  }
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
    var n_s1 := NormalizeBitString(s1);
    var n_s2 := NormalizeBitString(s2);

    if n_s1 == n_s2 {
        res := 0;
    } else if |n_s1| > |n_s2| {
        res := 1;
    } else if |n_s1| < |n_s2| {
        res := -1;
    } else { // |n_s1| == |n_s2|
        // Standard string comparison for equal length bit strings
        var i := 0;
        while i < |n_s1|
            invariant 0 <= i <= |n_s1|
            invariant forall k | 0 <= k < i :: n_s1[k] == n_s2[k]
            decreases |n_s1| - i
        {
            if n_s1[i] < n_s2[i] {
                return -1;
            } else if n_s1[i] > n_s2[i] {
                return 1;
            }
            i := i + 1;
        }
        res := 0;
    }
}
// </vc-code>

