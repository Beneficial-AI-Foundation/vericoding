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

lemma AllZerosZero(s: string)
  requires ValidBitString(s)
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    var spre := s[0..|s|-1];
    AllZerosZero(spre);
    // By definition of Str2Int
    assert Str2Int(s) == 2 * Str2Int(spre) + (if s[|s|-1] == '1' then 1 else 0);
    assert s[|s|-1] == '0';
    assert Str2Int(s) == 2 * Str2Int(spre);
    assert Str2Int(spre) == 0;
    assert Str2Int(s) == 0;
  }
}

lemma Str2IntConcat(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == Str2Int(a) * pow2(|b|) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
    // b == ""
    assert pow2(0) == 1;
    assert Str2Int(b) == 0;
    assert a + b == a;
    assert Str2Int(a + b) == Str2Int(a);
    assert Str2Int(a + b) == Str2Int(a) * pow2(0) + Str2Int(b);
  } else {
    var bpre := b[0..|b|-1];
    var last := b[|b|-1];
    Str2IntConcat(a, bpre);
    // (a+b)[0..|a+b|-1] is a + bpre
    assert (a + b)[0..|a + b| - 1] == a + bpre;
    assert Str2Int(a + b) == 2 * Str2Int(a + bpre) + (if last == '1' then 1 else 0);
    assert Str2Int(a + b) == 2 * (Str2Int(a) * pow2(|bpre|) + Str2Int(bpre)) + (if last == '1' then 1 else 0);
    assert Str2Int(a + b) == Str2Int(a) * (2 * pow2(|bpre|)) + (2 * Str2Int(bpre) + (if last == '1' then 1 else 0));
    assert 2 * pow2(|bpre|) == pow2(|b|);
    assert 2 * Str2Int(bpre) + (if last == '1' then 1 else 0) == Str2Int(b);
    assert Str2Int(a + b) == Str2Int(a) * pow2(|b|) + Str2Int(b);
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
  if (!ValidBitString(s)) {
    t := "0";
    return;
  }
  var i := 0;
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall j | 0 <= j < i :: s[j] == '0'
    decreases |s| - i
  {
    i := i + 1;
  }
  if i == |s| {
    // all zeros
    t := "0";
    // preserve value when s is a valid bitstring
    if ValidBitString(s) {
      AllZerosZero(s);
      // Str2Int("0") == 0 by definition
    }
    return;
  } else {
    t := s[i..|s|];
    if ValidBitString(s) {
      var a := s[0..i];
      var b := t;
      // a consists of zeros by the loop invariant
      AllZerosZero(a);
      // Use concatenation lemma: s == a + b
      Str2IntConcat(a, b);
      assert s == a + b;
      // From the two lemmas Str2Int(s) == Str2Int(a)*pow2(|b|)+Str2Int(b) and Str2Int(a)==0
      // we get Str2Int(s) == Str2Int(b) == Str2Int(t)
    }
    return;
  }
}
// </vc-code>

