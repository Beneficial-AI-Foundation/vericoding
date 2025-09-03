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
  // Handle empty strings
  if |s1| == 0 && |s2| == 0 {
    Str2IntEmpty();
    return 0;
  } else if |s1| == 0 {
    Str2IntEmpty();
    if |s2| > 0 && s2[0] == '1' {
      Str2IntPositive(s2);
    } else if |s2| == 1 && s2[0] == '0' {
      Str2IntSingle('0');
    }
    return -1;
  } else if |s2| == 0 {
    Str2IntEmpty();
    if |s1| > 0 && s1[0] == '1' {
      Str2IntPositive(s1);
    } else if |s1| == 1 && s1[0] == '0' {
      Str2IntSingle('0');
    }
    return 1;
  }
  
  // Remove leading zeros
  var start1 := 0;
  while start1 < |s1| - 1 && s1[start1] == '0'
    invariant 0 <= start1 < |s1|
    invariant forall i | 0 <= i < start1 :: s1[i] == '0'
  {
    start1 := start1 + 1;
  }
  
  var start2 := 0;
  while start2 < |s2| - 1 && s2[start2] == '0'
    invariant 0 <= start2 < |s2|
    invariant forall i | 0 <= i < start2 :: s2[i] == '0'
  {
    start2 := start2 + 1;
  }
  
  var norm1 := s1[start1..];
  var norm2 := s2[start2..];
  
  assert ValidBitString(norm1) && ValidBitString(norm2);
  assert |norm1| > 0 && |norm2| > 0;
  assert |norm1| > 1 ==> norm1[0] != '0';
  assert |norm2| > 1 ==> norm2[0] != '0';
  
  // Compare by length first
  if |norm1| < |norm2| {
    res := CompareUnequal(norm2, norm1);
    res := -res;
    return res;
  } else if |norm1| > |norm2| {
    res := CompareUnequal(norm1, norm2);
    return res;
  } else {
    // Same length - use lexicographic comparison
    LexCompareEqualLength(norm1, norm2);
    if norm1 < norm2 {
      return -1;
    } else if norm2 < norm1 {
      return 1;
    } else {
      return 0;
    }
  }
}
// </vc-code>

