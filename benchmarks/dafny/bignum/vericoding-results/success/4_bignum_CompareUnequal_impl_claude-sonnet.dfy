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
lemma Str2IntPositive(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s) >= 0
  ensures (exists i :: 0 <= i < |s| && s[i] == '1') ==> Str2Int(s) > 0
{
  if |s| == 1 {
    assert s[0] == '0' || s[0] == '1';
  } else {
    Str2IntPositive(s[0..|s|-1]);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
  }
}

lemma Str2IntNonLeadingZero(s: string)
  requires ValidBitString(s) && |s| > 0
  requires |s| > 1 ==> s[0] != '0'
  ensures (|s| == 1 && s[0] == '1') || |s| > 1 ==> Str2Int(s) >= 1
{
  if |s| == 1 {
    assert s[0] == '0' || s[0] == '1';
    if s[0] == '1' {
      assert Str2Int(s) == 1;
    }
  } else {
    assert s[0] != '0';
    assert s[0] == '1';
    var prefix := s[0..|s|-1];
    assert ValidBitString(prefix);
    Str2IntPositive(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) >= 1;
  }
}

lemma Str2IntBound(s: string)
  requires ValidBitString(s) && |s| > 0
  requires |s| > 1 ==> s[0] != '0'
  ensures (|s| == 1 && s[0] == '1') || |s| > 1 ==> Str2Int(s) >= 1
  ensures |s| > 1 ==> Str2Int(s) >= Str2IntPowerOf2(|s| - 1)
{
  Str2IntNonLeadingZero(s);
  if |s| > 1 {
    assert s[0] != '0';
    assert s[0] == '1';
    var prefix := s[0..|s|-1];
    assert ValidBitString(prefix);
    Str2IntPositive(prefix);
    assert Str2Int(prefix) >= 0;
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) >= 2 * Str2Int(prefix);
    assert Str2Int(s) >= 2 * 0;
    assert Str2IntPowerOf2(|s| - 1) == Str2IntPowerOf2(|prefix|);
    Str2IntPowerOf2Lemma(|prefix| - 1);
    if |prefix| > 0 {
      assert 2 * Str2IntPowerOf2(|prefix| - 1) == Str2IntPowerOf2(|prefix|);
      assert Str2Int(s) >= Str2IntPowerOf2(|s| - 1);
    } else {
      assert Str2IntPowerOf2(0) == 1;
      assert Str2Int(s) >= 1;
      assert Str2IntPowerOf2(|s| - 1) == 1;
    }
  }
}

ghost function Str2IntPowerOf2(n: nat): nat
{
  if n == 0 then 1 else 2 * Str2IntPowerOf2(n - 1)
}

lemma Str2IntPowerOf2Lemma(n: nat)
  ensures Str2IntPowerOf2(n + 1) == 2 * Str2IntPowerOf2(n)
{
}

lemma Str2IntPowerOf2Monotonic(i: nat, j: nat)
  requires i <= j
  ensures Str2IntPowerOf2(i) <= Str2IntPowerOf2(j)
{
  if i == j {
    assert Str2IntPowerOf2(i) == Str2IntPowerOf2(j);
  } else {
    Str2IntPowerOf2Monotonic(i, j - 1);
    Str2IntPowerOf2Lemma(j - 1);
    assert Str2IntPowerOf2(j) == 2 * Str2IntPowerOf2(j - 1);
    assert Str2IntPowerOf2(i) <= Str2IntPowerOf2(j - 1);
    assert Str2IntPowerOf2(i) <= 2 * Str2IntPowerOf2(j - 1);
  }
}

lemma Str2IntUpperBound(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s) < Str2IntPowerOf2(|s|)
{
  if |s| == 1 {
    assert s[0] == '0' || s[0] == '1';
    assert Str2Int(s) <= 1;
    assert Str2IntPowerOf2(1) == 2;
  } else {
    var prefix := s[0..|s|-1];
    Str2IntUpperBound(prefix);
    assert Str2Int(prefix) < Str2IntPowerOf2(|prefix|);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) <= 2 * Str2Int(prefix) + 1;
    assert Str2Int(s) < 2 * Str2IntPowerOf2(|prefix|) + 1;
    Str2IntPowerOf2Lemma(|prefix| - 1);
    assert 2 * Str2IntPowerOf2(|prefix|) == Str2IntPowerOf2(|prefix| + 1);
    assert |prefix| + 1 == |s|;
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
  Str2IntBound(s1);
  Str2IntBound(s2);
  Str2IntUpperBound(s2);
  
  assert |s1| > |s2|;
  assert |s1| >= |s2| + 1;
  assert |s1| - 1 >= |s2|;
  
  Str2IntPowerOf2Monotonic(|s2|, |s1| - 1);
  
  assert Str2Int(s2) < Str2IntPowerOf2(|s2|);
  assert |s1| > 1 ==> Str2Int(s1) >= Str2IntPowerOf2(|s1| - 1);
  assert Str2IntPowerOf2(|s2|) <= Str2IntPowerOf2(|s1| - 1);
  
  if |s1| == 1 {
    assert |s2| < |s1|;
    assert |s2| < 1;
    assert |s2| == 0;
    assert false;
  } else {
    assert Str2Int(s1) >= Str2IntPowerOf2(|s1| - 1);
    assert Str2IntPowerOf2(|s1| - 1) >= Str2IntPowerOf2(|s2|);
    assert Str2Int(s2) < Str2IntPowerOf2(|s2|);
    assert Str2Int(s1) > Str2Int(s2);
  }
  
  res := 1;
}
// </vc-code>

