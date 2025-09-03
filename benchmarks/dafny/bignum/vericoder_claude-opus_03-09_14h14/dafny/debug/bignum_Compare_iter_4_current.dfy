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
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntLeadingZero(s: string)
  requires ValidBitString(s)
  requires |s| > 0 && s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
  decreases |s|
{
  if |s| == 1 {
    assert s == "0";
    assert Str2Int(s) == 0;
    assert s[1..] == "";
    assert Str2Int(s[1..]) == 0;
  } else {
    calc {
      Str2Int(s);
      == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { assert s[0..|s|-1] == "0" + s[1..|s|-1]; }
      2 * Str2Int("0" + s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { 
        assert ValidBitString("0" + s[1..|s|-1]);
        assert |"0" + s[1..|s|-1]| > 0;
        assert ("0" + s[1..|s|-1])[0] == '0';
        Str2IntLeadingZero("0" + s[1..|s|-1]); 
      }
      2 * Str2Int(s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { assert s[1..] == s[1..|s|-1] + [s[|s|-1]]; 
           assert ValidBitString(s[1..]); }
      Str2Int(s[1..]);
    }
  }
}

lemma Str2IntComparison(s1: string, s2: string, i: nat)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  requires i < |s1|
  requires forall j | 0 <= j < i :: s1[j] == s2[j]
  requires s1[i] < s2[i]
  ensures Str2Int(s1) < Str2Int(s2)
  decreases |s1| - i
{
  if i == |s1| - 1 {
    assert s1[0..i] == s2[0..i];
    assert s1[i] == '0' && s2[i] == '1';
  } else {
    var n := |s1|;
    calc {
      Str2Int(s1);
      == 2 * Str2Int(s1[0..n-1]) + (if s1[n-1] == '1' then 1 else 0);
      <= { if s1[n-1] == s2[n-1] {
             Str2IntComparison(s1[0..n-1], s2[0..n-1], i);
           }
         }
      2 * Str2Int(s2[0..n-1]) + (if s2[n-1] == '1' then 1 else 0);
      == Str2Int(s2);
    }
  }
}

lemma Str2IntShorterSmaller(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| < |s2|
  requires |s2| > 0 && s2[0] == '1'
  ensures Str2Int(s1) < Str2Int(s2)
{
  if |s1| == 0 {
    assert Str2Int(s1) == 0;
    assert Str2Int(s2) > 0;
  } else {
    var minPowerOf2 := PowerOf2(|s2| - 1);
    Str2IntUpperBound(s1);
    if |s1| < |s2| - 1 {
      PowerOf2Bounds(|s1|, |s2| - 1);
      assert PowerOf2(|s1|) <= PowerOf2(|s2| - 1);
      assert Str2Int(s1) < PowerOf2(|s1|);
      assert Str2Int(s1) < minPowerOf2;
    } else {
      assert |s1| == |s2| - 1;
      assert Str2Int(s1) < PowerOf2(|s1|);
      assert PowerOf2(|s1|) == minPowerOf2;
      assert Str2Int(s1) < minPowerOf2;
    }
    Str2IntLowerBound(s2);
    assert Str2Int(s2) >= minPowerOf2;
  }
}

ghost function PowerOf2(n: nat): nat
{
  if n == 0 then 1 else 2 * PowerOf2(n - 1)
}

lemma PowerOf2Positive(n: nat)
  ensures PowerOf2(n) >= 1
{
  // By induction on n
}

lemma PowerOf2Bounds(m: nat, n: nat)
  requires m < n
  ensures PowerOf2(m) <= PowerOf2(n)
{
  if m == n - 1 {
    assert PowerOf2(n) == 2 * PowerOf2(m);
  } else {
    PowerOf2Bounds(m, n - 1);
  }
}

lemma Str2IntUpperBound(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < PowerOf2(|s|)
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
    assert PowerOf2(0) == 1;
  } else {
    calc {
      Str2Int(s);
      == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      < { Str2IntUpperBound(s[0..|s|-1]); }
      2 * PowerOf2(|s| - 1) + 1;
      <= { PowerOf2Positive(|s| - 1); assert PowerOf2(|s| - 1) >= 1; }
      2 * PowerOf2(|s| - 1) + PowerOf2(|s| - 1);
      == 3 * PowerOf2(|s| - 1);
      <= { assert 3 * PowerOf2(|s| - 1) <= 2 * PowerOf2(|s|); }
      2 * PowerOf2(|s|);
    }
    assert Str2Int(s) < 2 * PowerOf2(|s|);
    assert PowerOf2(|s|) == 2 * PowerOf2(|s| - 1);
    assert Str2Int(s) < PowerOf2(|s|);
  }
}

lemma Str2IntLowerBound(s: string)
  requires ValidBitString(s)
  requires |s| > 0 && s[0] == '1'
  ensures Str2Int(s) >= PowerOf2(|s| - 1)
  decreases |s|
{
  if |s| == 1 {
    assert s == "1";
    assert Str2Int(s) == 1;
    assert PowerOf2(0) == 1;
  } else {
    calc {
      Str2Int(s);
      == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      >= 2 * Str2Int(s[0..|s|-1]);
      >= { Str2IntLowerBound(s[0..|s|-1]); }
      2 * PowerOf2(|s| - 2);
      == PowerOf2(|s| - 1);
    }
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
  var s1' := s1;
  var s2' := s2;
  
  // Remove leading zeros
  while |s1'| > 0 && s1'[0] == '0'
    invariant ValidBitString(s1')
    invariant Str2Int(s1') == Str2Int(s1)
    decreases |s1'|
  {
    Str2IntLeadingZero(s1');
    s1' := s1'[1..];
  }
  
  while |s2'| > 0 && s2'[0] == '0'
    invariant ValidBitString(s2')
    invariant Str2Int(s2') == Str2Int(s2)
    decreases |s2'|
  {
    Str2IntLeadingZero(s2');
    s2' := s2'[1..];
  }
  
  // Compare lengths first
  if |s1'| < |s2'| {
    if |s2'| > 0 {
      Str2IntShorterSmaller(s1', s2');
    }
    return -1;
  } else if |s1'| > |s2'| {
    if |s1'| > 0 {
      Str2IntShorterSmaller(s2', s1');
    }
    return 1;
  }
  
  // Same length, compare lexicographically
  var i := 0;
  while i < |s1'|
    invariant 0 <= i <= |s1'|
    invariant |s1'| == |s2'|
    invariant forall j | 0 <= j < i :: s1'[j] == s2'[j]
    decreases |s1'| - i
  {
    if s1'[i] < s2'[i] {
      Str2IntComparison(s1', s2', i);
      return -1;
    } else if s1'[i] > s2'[i] {
      Str2IntComparison(s2', s1', i);
      return 1;
    }
    i := i + 1;
  }
  
  assert s1' == s2';
  return 0;
}
// </vc-code>

