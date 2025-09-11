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
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntSingle(c: char)
  requires c == '0' || c == '1'
  ensures Str2Int([c]) == if c == '1' then 1 else 0
{
  assert Str2Int([c]) == 2 * Str2Int([]) + (if c == '1' then 1 else 0);
}

lemma Str2IntPositive(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '1'
  ensures Str2Int(s) > 0
{
  if |s| == 1 {
    Str2IntSingle('1');
  } else {
    assert s == s[0..|s|-1] + [s[|s|-1]];
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert ValidBitString(s[0..|s|-1]);
    assert |s[0..|s|-1]| > 0;
    assert s[0..|s|-1][0] == s[0] == '1';
    Str2IntPositive(s[0..|s|-1]);
  }
}

lemma Str2IntBound(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < Power2(|s|)
  ensures |s| > 0 && s[0] == '1' ==> Str2Int(s) >= Power2(|s| - 1)
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
    assert Power2(0) == 1;
  } else {
    var prefix := s[0..|s|-1];
    var last := s[|s|-1];
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
    
    if |prefix| == 0 {
      assert Str2Int(prefix) == 0;
      assert Str2Int(s) <= 1;
      assert Power2(1) == 2;
      if s[0] == '1' {
        assert Str2Int(s) == 1;
        assert Power2(0) == 1;
      }
    } else {
      Str2IntBound(prefix);
      assert Str2Int(prefix) < Power2(|prefix|);
      assert |prefix| == |s| - 1;
      assert Str2Int(s) < 2 * Power2(|s| - 1) + 1;
      assert 2 * Power2(|s| - 1) == Power2(|s|);
      assert Str2Int(s) < Power2(|s|);
      
      if |s| > 0 && s[0] == '1' {
        if |prefix| > 0 {
          assert prefix[0] == s[0] == '1';
          assert Str2Int(prefix) >= Power2(|prefix| - 1);
          assert Str2Int(s) >= 2 * Power2(|prefix| - 1);
          assert |prefix| == |s| - 1;
          assert Str2Int(s) >= Power2(|s| - 1);
        }
      }
    }
  }
}

ghost function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

lemma LongerStringGreater(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > |s2|
  requires |s1| > 0 && (|s1| > 1 ==> s1[0] != '0')
  requires |s2| > 0 && (|s2| > 1 ==> s2[0] != '0')
  ensures Str2Int(s1) > Str2Int(s2)
{
  if |s1| == 1 {
    assert s1[0] == '0' || s1[0] == '1';
    assert |s2| == 0;
    Str2IntEmpty();
    assert Str2Int(s2) == 0;
    if s1[0] == '1' {
      Str2IntSingle('1');
      assert Str2Int(s1) == 1 > 0;
    } else {
      Str2IntSingle('0');
      assert Str2Int(s1) == 0;
    }
  } else {
    assert |s1| > 1;
    assert s1[0] != '0';
    assert s1[0] == '1';
    
    Str2IntBound(s1);
    assert Str2Int(s1) >= Power2(|s1| - 1);
    
    if |s2| > 0 {
      Str2IntBound(s2);
      assert Str2Int(s2) < Power2(|s2|);
      
      PowerMonotonic(|s2|, |s1| - 1);
      assert Power2(|s2|) <= Power2(|s1| - 1);
      assert Str2Int(s2) < Power2(|s2|) <= Power2(|s1| - 1) <= Str2Int(s1);
    } else {
      Str2IntEmpty();
      assert Str2Int(s2) == 0;
      Str2IntPositive(s1);
      assert Str2Int(s1) > 0;
    }
  }
}

lemma PowerMonotonic(m: nat, n: nat)
  requires m <= n
  ensures Power2(m) <= Power2(n)
{
  if m == n {
    assert Power2(m) == Power2(n);
  } else {
    assert m < n;
    PowerMonotonic(m, n - 1);
    assert Power2(m) <= Power2(n - 1);
    assert Power2(n) == 2 * Power2(n - 1);
    assert Power2(n - 1) < Power2(n);
    assert Power2(m) <= Power2(n);
  }
}

lemma LexCompareEqualLength(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  ensures s1 < s2 ==> Str2Int(s1) < Str2Int(s2)
  ensures s1 == s2 ==> Str2Int(s1) == Str2Int(s2)
  ensures s2 < s1 ==> Str2Int(s1) > Str2Int(s2)
  decreases |s1|
{
  if |s1| == 0 {
    assert s1 == s2 == "";
  } else if |s1| == 1 {
    Str2IntSingle(s1[0]);
    Str2IntSingle(s2[0]);
  } else {
    var prefix1 := s1[0..|s1|-1];
    var prefix2 := s2[0..|s2|-1];
    var last1 := s1[|s1|-1];
    var last2 := s2[|s2|-1];
    
    assert Str2Int(s1) == 2 * Str2Int(prefix1) + (if last1 == '1' then 1 else 0);
    assert Str2Int(s2) == 2 * Str2Int(prefix2) + (if last2 == '1' then 1 else 0);
    
    if prefix1 < prefix2 {
      LexCompareEqualLength(prefix1, prefix2);
      assert Str2Int(prefix1) < Str2Int(prefix2);
    } else if prefix2 < prefix1 {
      LexCompareEqualLength(prefix1, prefix2);
      assert Str2Int(prefix1) > Str2Int(prefix2);
    } else {
      assert prefix1 == prefix2;
      LexCompareEqualLength(prefix1, prefix2);
      assert Str2Int(prefix1) == Str2Int(prefix2);
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
  LongerStringGreater(s1, s2);
  return 1;
}
// </vc-code>

