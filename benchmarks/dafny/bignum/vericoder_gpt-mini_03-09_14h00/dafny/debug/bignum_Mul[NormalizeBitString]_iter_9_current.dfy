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
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
method IntToBitString(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  ensures |s| > 0
  ensures |s| > 1 ==> s[0] != '0'
{
  if n == 0 {
    s := "0";
    return;
  }

  var p := 1;
  // compute p = largest power of two <= n
  while p * 2 <= n
    decreases n - p
    invariant 1 <= p <= n
  {
    p := p * 2;
  }

  var rem := n - p;
  // first bit is '1'
  s := "1";

  // establish invariants at loop entry
  assert 0 <= rem;
  // from loop exit condition p*2 > n, we get n < 2*p, hence rem = n - p < p
  assert n < 2 * p;
  assert rem < p;
  // prove Str2Int(s) == 1
  assert ValidBitString(s);
  assert |s| == 1;
  assert s[0] == '1';
  assert Str2Int(s) == (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  assert Str2Int(s[0..|s|-1]) == 0;
  assert Str2Int(s) == 1;
  // so Str2Int(s) * p + rem == 1 * p + (n - p) == n
  assert Str2Int(s) * p + rem == n;

  // invariant: ValidBitString(s), 0 <= rem < p, s[0] == '1', and Str2Int(s) * p + rem == n
  while p > 1
    decreases p
    invariant ValidBitString(s)
    invariant 0 <= rem < p
    invariant s[0] == '1'
    invariant Str2Int(s) * p + rem == n
  {
    var half := p / 2;
    var oldS := s;
    var oldRem := rem;
    if rem >= half {
      s := oldS + "1";
      rem := oldRem - half;

      // prove Str2Int(s) == 2 * Str2Int(oldS) + 1
      assert |s| > 0;
      assert s[0..|s|-1] == oldS;
      assert s[|s|-1] == '1';
      assert Str2Int(s) == (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
      assert Str2Int(s) == 2 * Str2Int(oldS) + 1;

      // prove ValidBitString(s) by showing each character is '0' or '1'
      var k := 0;
      while k < |s|
        decreases |s| - k
      {
        if k < |oldS| {
          assert s[k] == oldS[k];
          assert oldS[k] == '0' || oldS[k] == '1';
          assert s[k] == '0' || s[k] == '1';
        } else {
          assert k == |oldS|;
          assert s[k] == '1';
        }
        k := k + 1;
      }
    } else {
      s := oldS + "0";
      // rem unchanged

      // prove Str2Int(s) == 2 * Str2Int(oldS)
      assert |s| > 0;
      assert s[0..|s|-1] == oldS;
      assert s[|s|-1] == '0';
      assert Str2Int(s) == (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
      assert Str2Int(s) == 2 * Str2Int(oldS);

      // prove ValidBitString(s)
      var k2 := 0;
      while k2 < |s|
        decreases |s| - k2
      {
        if k2 < |oldS| {
          assert s[k2] == oldS[k2];
          assert oldS[k2] == '0' || oldS[k2] == '1';
          assert s[k2] == '0' || s[k2] == '1';
        } else {
          assert k2 == |oldS|;
          assert s[k2] == '0';
        }
        k2 := k2 + 1;
      }
    }
    p := half;
    // Now show the numeric invariant holds with the new p
    assert Str2Int(s) * p + rem == n;
    // and the bounds on rem with new p
    assert 0 <= rem;
    assert rem < p;
    // and the prefix bit remains '1'
    assert s[0] == '1';
  }

  // after loop p == 1
  assert p == 1;
  // from invariant 0 <= rem < p and p == 1 we get rem == 0
  assert rem == 0;
  assert Str2Int(s) * 1 + 0 == n;
  assert Str2Int(s) == n;

  // ensure no leading zero when length > 1
  if |s| > 1 {
    // first bit must be '1' because we started with the highest power <= n
    assert s[0] == '1';
  }
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var a: nat := 0;
  var i: nat := 0;
  while i < |s1|
    decreases |s1| - i
    invariant 0 <= i <= |s1|
    invariant ValidBitString(s1[0..i])
    invariant a == Str2Int(s1[0..i])
  {
    var bit := if s1[i] == '1' then 1 else 0;
    var newa := 2 * a + bit;
    // By lemma, Str2Int(s1[0..i+1]) == 2*Str2Int(s1[0..i]) + bit
    Str2IntPrefixStep(s1, i);
    // Now newa == Str2Int(s1[0..i+1])
    assert newa == Str2Int(s1[0..i+1]);
    a := newa;
    ValidPrefixIsValid(s1, i + 1);
    i := i + 1;
  }
  // at loop exit, i == |s1| and therefore a == Str2Int(s1)
  assert a == Str2Int(s1);

  var b: nat := 0;
  i := 0;
  while i < |s2|
    decreases |s2| - i
    invariant 0 <= i <= |s2|
    invariant ValidBitString(s2[0..i])
    invariant b == Str2Int(s2[0..i])
  {
    var bit := if s2[i] == '1' then 1 else 0;
    var newb := 2 * b + bit;
    Str2IntPrefixStep(s2, i);
    assert newb == Str2Int(s2[0..i+1]);
    b := newb;
    ValidPrefixIsValid(s2, i + 1);
    i := i + 1;
  }
  // at loop exit, i == |s2| and therefore b == Str2Int(s2)
  assert b == Str2Int(s2);

  var p: nat := a * b;
  // ensure the IntToBitString postconditions will yield the required result
  res := IntToBitString(p);
  // IntToBitString ensures Str2Int(res) == p and ValidBitString(res)
  assert Str2Int(res) == p;
  assert p == Str2Int(s1) * Str2Int(s2);
}
// </vc-code>

