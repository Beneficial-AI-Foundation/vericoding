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

lemma Str2IntConcat(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == pow2(|b|) * Str2Int(a) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
    // b == ""
    assert a + b == a;
    assert pow2(0) * Str2Int(a) + Str2Int(b) == Str2Int(a);
    assert Str2Int(a + b) == Str2Int(a);
  } else {
    var bpref := b[0..|b| - 1];
    var last := b[|b| - 1 .. |b|];
    // a + b == (a + bpref) + last
    assert a + b == (a + bpref) + last;
    RemoveSingleLast(a + bpref, last);
    assert (a + b)[0..|a + b| - 1] == a + bpref;
    // expand Str2Int(a + b)
    assert Str2Int(a + b) == 2 * Str2Int(a + bpref) + (if b[|b|-1] == '1' then 1 else 0);
    // recurse on bpref
    Str2IntConcat(a, bpref);
    assert Str2Int(a + bpref) == pow2(|bpref|) * Str2Int(a) + Str2Int(bpref);
    // pow2(|b|) == 2 * pow2(|bpref|)
    calc {
      pow2(|b|);
      == { assert |b| == |bpref| + 1; apply Pow2Succ(|bpref|); }
      2 * pow2(|bpref|);
    }
    assert pow2(|b|) == 2 * pow2(|bpref|);
    // combine
    assert 2 * Str2Int(a + bpref) + (if b[|b|-1] == '1' then 1 else 0)
           == 2 * (pow2(|bpref|) * Str2Int(a) + Str2Int(bpref)) + (if b[|b|-1] == '1' then 1 else 0);
    assert 2 * (pow2(|bpref|) * Str2Int(a)) + 2 * Str2Int(bpref) + (if b[|b|-1] == '1' then 1 else 0)
           == pow2(|b|) * Str2Int(a) + (2 * Str2Int(bpref) + (if b[|b|-1] == '1' then 1 else 0));
    assert 2 * Str2Int(bpref) + (if b[|b|-1] == '1' then 1 else 0) == Str2Int(b);
    assert Str2Int(a + b) == pow2(|b|) * Str2Int(a) + Str2Int(b);
  }
}

lemma RemoveLeadingZero(x: string)
  requires ValidBitString(x)
  ensures Str2Int("0" + x) == Str2Int(x)
  decreases |x|
{
  // Use concatenation lemma with a = "0"
  Str2IntConcat("0", x);
  // Str2Int("0") == 0
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
    // trivial, nothing to prove
  } else {
    // first character is '0'
    assert s[0] == '0';
    var s1 := s[1..|s|];
    // Let a be the first character as length-1 string
    var a := s[0..1];
    // s == a + s1
    assert s == a + s1;
    // a is "0", so Str2Int(a) == 0
    assert Str2Int("") == 0;
    assert
// </vc-helpers>

// <vc-spec>
method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
// </vc-spec>
// <vc-code>
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

lemma Str2IntConcat(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == pow2(|b|) * Str2Int(a) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
    // b == ""
    assert a + b == a;
    assert pow2(0) * Str2Int(a) + Str2Int(b) == Str2Int(a);
    assert Str2Int(a + b) == Str2Int(a);
  } else {
    var bpref := b[0..|b| - 1];
    var last := b[|b| - 1 .. |b|];
    // a + b == (a + bpref) + last
    assert a + b == (a + bpref) + last;
    RemoveSingleLast(a + bpref, last);
    assert (a + b)[0..|a + b| - 1] == a + bpref;
    // expand Str2Int(a + b)
    assert Str2Int(a + b) == 2 * Str2Int(a + bpref) + (if b[|b|-1] == '1' then 1 else 0);
    // recurse on bpref
    Str2IntConcat(a, bpref);
    assert Str2Int(a + bpref) == pow2(|bpref|) * Str2Int(a) + Str2Int(bpref);
    // pow2(|b|) == 2 * pow2(|bpref|)
    calc {
      pow2(|b|);
      == { assert |b| == |bpref| + 1; apply Pow2Succ(|bpref|); }
      2 * pow2(|bpref|);
    }
    assert pow2(|b|) == 2 * pow2(|bpref|);
    // combine
    assert 2 * Str2Int(a + bpref) + (if b[|b|-1] == '1' then 1 else 0)
           == 2 * (pow2(|bpref|) * Str2Int(a) + Str2Int(bpref)) + (if b[|b|-1] == '1' then 1 else 0);
    assert 2 * (pow2(|bpref|) * Str2Int(a)) + 2 * Str2Int(bpref) + (if b[|b|-1] == '1' then 1 else 0)
           == pow2(|b|) * Str2Int(a) + (2 * Str2Int(bpref) + (if b[|b|-1] == '1' then 1 else 0));
    assert 2 * Str2Int(bpref) + (if b[|b|-1] == '1' then 1 else 0) == Str2Int(b);
    assert Str2Int(a + b) == pow2(|b|) * Str2Int(a) + Str2Int(b);
  }
}

lemma RemoveLeadingZero(x: string)
  requires ValidBitString(x)
  ensures Str2Int("0" + x) == Str2Int(x)
  decreases |x|
{
  // Use concatenation lemma with a = "0"
  Str2IntConcat("0", x);
  // Str2Int("0") == 0
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
    // trivial, nothing to prove
  } else {
    // first character is '0'
    assert s[0] == '0';
    var s1 := s[1..|s|];
    // Let a be the first character as length-1 string
    var a := s[0..1];
    // s == a + s1
    assert s == a + s1;
    // a is "0", so Str2Int(a) == 0
    assert Str2Int("") == 0;
    assert
// </vc-code>

