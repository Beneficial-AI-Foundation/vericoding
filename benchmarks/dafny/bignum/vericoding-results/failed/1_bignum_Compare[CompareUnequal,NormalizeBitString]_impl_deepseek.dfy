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
lemma CompareLengthLemma(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > |s2|
  ensures Str2Int(s1) > Str2Int(s2)
  decreases |s2|
{
  if |s2| == 0 {
    assert Str2Int(s2) == 0;
    assert Str2Int(s1) > 0;
  } else if |s1| > |s2| + 1 {
    var s1_head := s1[0..|s1|-1];
    assert ValidBitString(s1_head);
    assert |s1_head| > |s2|;
    CompareLengthLemma(s1_head, s2);
    assert Str2Int(s1) >= 2 * Str2Int(s1_head);
    assert 2 * Str2Int(s1_head) > Str2Int(s2);
  } else if |s1| == |s2| + 1 {
    var s1_tail := s1[1..];
    assert ValidBitString(s1_tail);
    assert |s1_tail| == |s2|;
    CompareFromLeft(s1_tail, s2);
    assert Str2Int(s1) == 2 * Str2Int(s1_tail) + (if s1[0] == '1' then 1 else 0);
    assert 2 * Str2Int(s1_tail) >= Str2Int(s2);
    if s1[0] == '1' {
      assert Str2Int(s1) == 2 * Str2Int(s1_tail) + 1;
      assert Str2Int(s1) > 2 * Str2Int(s1_tail) >= Str2Int(s2);
    } else {
      assert s1[0] == '0';
      assert Str2Int(s1) == 2 * Str2Int(s1_tail);
      assert Str2Int(s1) == 2 * Str2Int(s1_tail) >= Str2Int(s2);
      if Str2Int(s1) == Str2Int(s2) {
        assert |s1| > |s2|;
        assert false; // Contradiction: different lengths but equal values
      }
    }
  }
}

lemma CompareEqualLength(s1: string, s2: string, k: nat)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| == k > 0
  requires s1[0] == '1' && s2[0] == '0'
  ensures Str2Int(s1) > Str2Int(s2)
{
  var s1_tail := s1[1..];
  var s2_tail := s2[1..];
  assert ValidBitString(s1_tail) && ValidBitString(s2_tail);
  assert |s1_tail| == |s2_tail| == k-1;
  
  CompareFromLeft(s1_tail, s2_tail);
  assert Str2Int(s1) == 2 * Str2Int(s1_tail) + 1;
  assert Str2Int(s2) == 2 * Str2Int(s2_tail);
  assert Str2Int(s1_tail) >= Str2Int(s2_tail);
  assert 2 * Str2Int(s1_tail) + 1 > 2 * Str2Int(s2_tail);
}

lemma CompareFromLeft(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  ensures Str2Int(s1) >= Str2Int(s2)
  decreases |s1|
{
  if |s1| == 0 {
    assert Str2Int(s1) == 0 && Str2Int(s2) == 0;
  } else if s1[0] == '1' && s2[0] == '0' {
    CompareEqualLength(s1, s2, |s1|);
  } else if s1[0] == '0' && s2[0] == '1' {
    CompareEqualLength(s2, s1, |s2|);
    assert Str2Int(s2) > Str2Int(s1); // So s1 < s2, which means s1 >= s2 is false
    assert false; // This case shouldn't occur when proving s1 >= s2
  } else {
    var s1_tail := s1[1..];
    var s2_tail := s2[1..];
    assert ValidBitString(s1_tail) && ValidBitString(s2_tail);
    assert |s1_tail| == |s2_tail|;
    CompareFromLeft(s1_tail, s2_tail);
    
    if s1[0] == s2[0] {
      assert Str2Int(s1) == 2 * Str2Int(s1_tail) + (if s1[0] == '1' then 1 else 0);
      assert Str2Int(s2) == 2 * Str2Int(s2_tail) + (if s2[0] == '1' then 1 else 0);
      assert Str2Int(s1_tail) >= Str2Int(s2_tail);
      assert Str2Int(s1) >= Str2Int(s2);
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
  var len1 := |s1|;
  var len2 := |s2|;
  if len1 > len2 {
    CompareLengthLemma(s1, s2);
    res := 1;
  } else if len1 < len2 {
    CompareLengthLemma(s2, s1);
    res := -1;
  } else if s1 == s2 {
    res := 0;
  } else {
    var s1_tail := s1[1..];
    var s2_tail := s2[1..];
    assert ValidBitString(s1_tail) && ValidBitString(s2_tail);
    res := Compare(s1_tail, s2_tail);
    if res == 0 {
      if s1[0] == '1' && s2[0] == '0' {
        res := 1;
      } else if s1[0] == '0' && s2[0] == '1' {
        res := -1;
      } else {
        res := 0;
      }
    } else if res > 0 {
      res := 1;
    } else {
      res := -1;
    }
  }
}
// </vc-code>

