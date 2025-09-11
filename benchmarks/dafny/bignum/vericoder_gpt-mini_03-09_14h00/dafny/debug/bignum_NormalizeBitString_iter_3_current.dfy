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

// <vc-helpers>
function pow2(k: nat): nat
  decreases k
{
  if k == 0 then 1 else 2 * pow2(k - 1)
}

lemma Pow2Succ(k: nat)
  ensures pow2(k + 1) == 2 * pow2(k)
{
  if k == 0 {
    assert pow2(1) == 2;
    assert pow2(0) == 1;
  } else {
    // By definition
    assert pow2(k + 1) == 2 * pow2(k);
  }
}

lemma RemoveSingleLast(x: string, tail: string)
  requires |tail| == 1
  ensures (x + tail)[0..|x + tail| - 1] == x
{
  assert |x + tail| == |x| + 1;
  assert |x + tail| - 1 == |x|;
  assert (x + tail)[0..|x|] == x;
}

lemma RemoveLeadingZero(x: string)
  requires ValidBitString(x)
  ensures Str2Int("0" + x) == Str2Int(x)
  decreases |x|
{
  if |x| == 0 {
    // Str2Int("") == 0 and Str2Int("0") == 0
    assert Str2Int("0" + x) == Str2Int(x);
  } else {
    var pref := x[0..|x| - 1];
    // pref has smaller length, so we can recurse
    RemoveLeadingZero(pref);
    // Expand definitions of Str2Int on both sides
    assert Str2Int("0" + x) == 2 * Str2Int("0" + pref) + (if x[|x| - 1] == '1' then 1 else 0);
    assert Str2Int(x) == 2 * Str2Int(pref) + (if x[|x| - 1] == '1' then 1 else 0);
    assert 2 * Str2Int("0" + pref) == 2 * Str2Int(pref);
    calc {
      Str2Int("0" + x);
      == { }
      2 * Str2Int("0" + pref) + (if x[|x| - 1] == '1' then 1 else 0);
      == { assert 2 * Str2Int("0" + pref) == 2 * Str2Int(pref); }
      2 * Str2Int(pref) + (if x[|x| - 1] == '1' then 1 else 0);
      == { }
      Str2Int(x);
    }
  }
}

lemma RemoveLeadingZerosN(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  requires forall k | 0 <= k < i :: s[k] == '0'
  ensures Str2Int(s) == (if i == |s| then 0 else Str2Int(s[i..|s|]))
  decreases i
{
  if i == 0 {
    // trivial
    assert Str2Int(s) == (if 0 == |s| then 0 else Str2Int(s[0..|s|]));
  } else {
    // first character is '0'
    assert s[0] == '0';
    var s1 := s[1..|s|];
    // s = "0" + s1
    // Show Str2Int(s) == Str2Int(s1)
    // ValidBitString(s1) holds
    RemoveLeadingZero(s1);
    assert Str2Int(s) == Str2Int(s1);
    // Now apply lemma to s1 with i-1
    RemoveLeadingZerosN(s1, i - 1);
    if i - 1 == |s1| {
      // then i == |s|
      assert Str2Int(s1) == 0;
      assert Str2Int(s) == 0;
    } else {
      // i-1 < |s1|, so result gives Str2Int(s1) == Str2Int(s1[i-1..|s1|])
      assert Str2Int(s) == Str2Int(s1[i - 1 .. |s1|]);
      // s[i..|s|] equals s1[i-1..|s1|]
      assert s[i..|s|] == s1[i - 1 .. |s1|];
      assert Str2Int(s) == Str2Int(s[i..|s|]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
// </vc-spec>
// <vc-code>
{
  if !ValidBitString(s) {
    t := "0";
    return;
  }
  if |s| == 0 {
    t := "0";
    return;
  }
  var i := 0;
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall k | 0 <= k < i :: s[k] == '0'
    decreases |s| - i
  {
    i := i + 1;
  }
  if i == |s| {
    // all zeros
    t := "0";
    // Prove equality of values when original string is all zeros
    RemoveLeadingZerosN(s, i);
    // by lemma Str2Int(s) == 0 and Str2Int("0") == 0
    return;
  } else {
    // first non-zero at position i
    t := s[i..|s|];
    // Prove values equal
    RemoveLeadingZerosN(s, i);
    return;
  }
}
// </vc-code>

