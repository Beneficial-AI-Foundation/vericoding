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

lemma Str2IntSnoc(x: string, last: string)
  requires ValidBitString(x) && ValidBitString(last) && |last| == 1
  ensures Str2Int(x + last) == 2 * Str2Int(x) + (if last[0] == '1' then 1 else 0)
{
  // (x + last) has last char last[0] and prefix x
  assert |x + last| == |x| + 1;
  RemoveSingleLast(x, last);
  assert (x + last)[0..|x + last| - 1] == x;
  assert (x + last)[|x + last| - 1] == last[0];
  // unfold Str2Int on x + last
  assert Str2Int(x + last) == 2 * Str2Int((x + last)[0..|x + last| - 1]) + (if (x + last)[|x + last| - 1] == '1' then 1 else 0);
  assert Str2Int(x + last) == 2 * Str2Int(x) + (if last[0] == '1' then 1 else 0);
}

lemma Str2IntConcat(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == pow2(|b|) * Str2Int(a) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
    assert a + b == a;
    assert Str2Int(a + b) == Str2Int(a);
    assert pow2(0) * Str2Int(a) + Str2Int(b) == Str2Int(a);
  } else {
    var bpref := b[0..|b| - 1];
    var last := b[|b| - 1 .. |b|];
    assert b == bpref + last;
    // Use snoc lemma on a+bpref and on bpref
    Str2IntSnoc(a + bpref, last);
    Str2IntConcat(a, bpref);
    Str2IntSnoc(bpref, last);
    // assemble equalities
    assert Str2Int(a + b) == 2 * Str2Int(a + bpref) + (if last[0] == '1' then 1 else 0);
    assert Str2Int(b) == 2 * Str2Int(bpref) + (if last[0] == '1' then 1 else 0);
    assert Str2Int(a + bpref) == pow2(|bpref|) * Str2Int(a) + Str2Int(bpref);
    // relate pow2 lengths
    assert |b| == |bpref| + 1;
    Pow2Succ(|bpref|);
    assert pow2(|b|) == 2 * pow2(|bpref|);
    // combine algebraically
    assert Str2Int(a + b)
           == 2 * (pow2(|bpref|) * Str2Int(a) + Str2Int(bpref)) + (if last[0] == '1' then 1 else 0);
    assert Str2Int(a + b)
           == (2 * pow2(|bpref|)) * Str2Int(a) + (2 * Str2Int(bpref) + (if last[0] == '1' then 1 else 0));
    assert 2 * Str2Int(bpref) + (if last[0] == '1' then 1 else 0) == Str2Int(b);
    assert Str2Int(a + b) == pow2(|b|) * Str2Int(a) + Str2Int(b);
  }
}

lemma RemoveLeadingZero(x: string)
  requires ValidBitString(x)
  ensures Str2Int("0" + x) == Str2Int(x)
  decreases |x|
{
  Str2IntConcat("0", x);
  assert Str2Int("") == 0;
  assert Str2Int("0") == 2 * Str2Int("") + (if "0"[0] == '1' then 1 else 0);
  assert Str2Int("0") == 0;
  assert pow2(|x|) * Str2Int("0") == 0;
  assert Str2Int("0" + x) == pow2(|x|) * Str2Int("0") + Str2Int(x);
  assert Str2Int("0" + x) == Str2Int(x);
}

lemma RemoveLeadingZerosN(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  requires forall k | 0 <= k < i :: s[k] == '0'
  ensures Str2Int(s) == (if i == |s| then 0 else Str2Int(s[i..|s|]))
  decreases i
{
  if i == 0 {
    if |s| == 0 {
      assert Str2Int(s) == 0;
    } else {
      // s[0..|s|] == s and thus RHS simplifies to Str2Int(s)
      assert s[0..|s|] == s;
      assert Str2Int(s) == Str2Int(s[0..|s|]);
    }
  } else {
    var s1 := s[1..|s|];
    var a := s[0..1];
    assert s == a + s1;
    assert |a| == 1;
    assert a[0] == '0';
    assert ValidBitString(a);
    // Str2Int(a) == 0
    assert Str2Int("") == 0;
    assert Str2Int(a) == 2 * Str2Int("") + (if a[0] == '1' then 1 else 0);
    assert Str2Int(a) == 0;
    // Use concat lemma to reduce Str2Int(s) to Str2Int(s1)
    Str2IntConcat(a, s1);
    assert Str2Int(s) == pow2(|s1|) * Str2Int(a) + Str2Int(s1);
    assert pow2(|s1|) * Str2Int(a) == 0;
    assert Str2Int(s) == Str2Int(s1);
    // apply induction on s1 with i-1
    RemoveLeadingZerosN(s1, i - 1);
    assert Str2Int(s1) == (if i - 1 == |s1| then 0 else Str2Int(s1[(i - 1)..|s1|]));
    assert |s1| == |s| - 1;
    if i - 1 == |s1| {
      assert i == |s|;
      assert Str2Int(s) == 0;
    } else {
      assert s1[(i - 1)..|s1|] == s[i..|s|];
      assert Str2Int(s1) == Str2Int(s[i..|s|]);
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
  // If input not a valid bit string, return "0" (arbitrary valid output)
  if !ValidBitString(s) {
    t := "0";
    return;
  }

  if |s| == 0 {
    t := "0";
    return;
  }

  // find first index i with s[i] == '1', or i == |s|
  var i := 0;
  while i < |s| && s[i] == '0'
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant forall k | 0 <= k < i :: s[k] == '0'
  {
    i := i + 1;
  }

  if i == |s| {
    // all zeros -> normalized to "0"
    t := "0";
    // prove the numeric equality when s is valid
    RemoveLeadingZerosN(s, i);
    // Str2Int("0") == 0 holds by direct expansion
    assert Str2Int("") == 0;
    assert Str2Int("0") == 2 * Str2Int("") + (if "0"[0] == '1' then 1 else 0);
    assert Str2Int("0") == 0;
    assert Str2Int(s) == 0;
    assert Str2Int(t) == 0;
  } else {
    // there is a leading '1' at position i
    t := s[i..|s|];
    // t is non-empty substring of a valid bitstring, hence valid
    assert |t| > 0;
    assert ValidBitString(t);
    // first char of t is '1' (loop exits when s[i] != '0', and ValidBitString implies it's '1')
    assert s[i] != '0';
    assert s[i] == '1';
    assert t[0] == '1';
    // Now relate numeric values
    RemoveLeadingZerosN(s, i);
    assert Str2Int(s) == (if i == |s| then 0 else Str2Int(s[i..|s|]));
    assert Str2Int(s) == Str2Int(t);
  }
}
// </vc-code>

