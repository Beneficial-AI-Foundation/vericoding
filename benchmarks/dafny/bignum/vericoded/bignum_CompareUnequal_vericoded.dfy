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
lemma LongerStringGreaterValue(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > |s2| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 1 ==> s2[0] != '0'
  ensures Str2Int(s1) > Str2Int(s2)
{
  // A string of length n with no leading zeros has value >= 2^(n-1)
  // A string of length m has value < 2^m
  // Since n > m, we have 2^(n-1) >= 2^m > value of s2
  
  var n := |s1|;
  var m := |s2|;
  
  // First, establish bounds for s1 and s2
  LowerBoundNoLeadingZero(s1);
  UpperBoundBitString(s2);
  
  // Since n > m, we have 2^(n-1) >= 2^m
  PowerMonotonic(m, n-1);
}

lemma LowerBoundNoLeadingZero(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires |s| > 1 ==> s[0] != '0'
  ensures |s| == 1 ==> Str2Int(s) >= 0
  ensures |s| > 1 ==> Str2Int(s) >= Power2(|s| - 1)
{
  if |s| == 1 {
    // Base case: single digit
    assert s[0] == '0' || s[0] == '1';
  } else {
    // s[0] must be '1' since it's not '0'
    assert s[0] == '1';
    
    // Str2Int(s) = 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
    // Since s[0] == '1', the prefix s[0..|s|-1] starts with '1'
    // We need to show this gives us at least 2^(|s|-1)
    
    var prefix := s[0..|s|-1];
    assert |prefix| == |s| - 1;
    assert prefix[0] == s[0] == '1';
    
    if |prefix| == 1 {
      assert prefix == "1";
      assert Str2Int(prefix) == 1;
      assert Str2Int(s) >= 2 * 1 == 2 == Power2(1);
    } else {
      LowerBoundNoLeadingZero(prefix);
      assert Str2Int(prefix) >= Power2(|prefix| - 1);
      assert Str2Int(s) >= 2 * Power2(|prefix| - 1) == Power2(|prefix|) == Power2(|s| - 1);
    }
  }
}

lemma UpperBoundBitString(s: string)
  requires ValidBitString(s)
  requires |s| >= 0
  ensures Str2Int(s) < Power2(|s|)
{
  if |s| == 0 {
    assert Str2Int(s) == 0 < 1 == Power2(0);
  } else {
    var prefix := s[0..|s|-1];
    UpperBoundBitString(prefix);
    assert Str2Int(prefix) < Power2(|prefix|);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) <= 2 * Str2Int(prefix) + 1;
    assert Str2Int(s) < 2 * Power2(|prefix|) == Power2(|prefix| + 1) == Power2(|s|);
  }
}

function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

lemma PowerMonotonic(m: nat, n: nat)
  requires m <= n
  ensures Power2(m) <= Power2(n)
{
  if m == n {
    // Base case
  } else {
    PowerMonotonic(m, n - 1);
    assert Power2(n) == 2 * Power2(n - 1) >= Power2(m);
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
  LongerStringGreaterValue(s1, s2);
  assert Str2Int(s1) > Str2Int(s2);
  res := 1;
}
// </vc-code>

