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
  // compute p = smallest power of two strictly greater than n
  while p <= n
    decreases n - p
  {
    p := p * 2;
  }

  var rem := n;
  s := "";
  // invariant: ValidBitString(s), 0 <= rem < p, and Str2Int(s) * p + rem == n
  while p > 1
    decreases p
    invariant ValidBitString(s)
    invariant 0 <= rem < p
    invariant Str2Int(s) * p + rem == n
  {
    // halve p, then decide next bit
    p := p / 2;
    if rem >= p {
      var oldS := s;
      var oldRem := rem;
      s := oldS + "1";
      rem := oldRem - p;

      // prove Str2Int(s) == 2 * Str2Int(oldS) + 1
      assert |s| > 0;
      assert s[0..|s|-1] == oldS;
      assert Str2Int(s) == (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
      assert s[|s|-1] == '1';
      assert Str2Int(s) == 2 * Str2Int(oldS) + 1;
    } else {
      var oldS := s;
      s := oldS + "0";
      // rem unchanged

      // prove Str2Int(s) == 2 * Str2Int(oldS)
      assert |s| > 0;
      assert s[0..|s|-1] == oldS;
      assert s[|s|-1] == '0';
      assert Str2Int(s) == (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
      assert Str2Int(s) == 2 * Str2Int(oldS);
    }
    // the invariant Str2Int(s) * p + rem == n follows from the above equalities and the previous invariant
  }

  // after loop p == 1
  assert p == 1;
  // from invariant 0 <= rem < p and p == 1 we get rem == 0
  assert rem == 0;
  assert Str2Int(s) * 1 + 0 == n;
  assert Str2Int(s) == n;

  // ensure no leading zero when length > 1
  if |s| > 1 {
    // first bit must be '1' because p was the smallest power of two > n
    assert s[0] == '1';
  }
}

lemma ValidPrefixIsValid(s: string, i: nat)
  requires ValidBitString(s)
  requires i <= |s|
  ensures ValidBitString(s[0..i])
{
  var k := 0;
  while k < |s[0..i]|
    decreases |s[0..i]| - k
  {
    // k < |s[0..i]| implies k < i and hence k < |s|
    assert 0 <= k < |s|;
    // from ValidBitString(s)
    assert s[k] == '0' || s[k] == '1';
    // substring property: prefix indexed at k equals s[k]
    assert (s[0..i])[k] == s[k];
    // therefore prefix char is '0' or '1'
    assert (s[0..i])[k] == '0' || (s[0..i])[k] == '1';
    k := k + 1;
  }
}

lemma Str2IntPrefixStep(s: string, j: nat)
  requires ValidBitString(s)
  requires j + 1 <= |s|
  ensures Str2Int(s[0..j+1]) == 2 * Str2Int(s[0..j]) + (if s[j] == '1' then 1 else 0)
{
  assert Str2Int(s[0..j+1]) == (if |s[0..j+1]| == 0 then 0 else 2 * Str2Int((s[0..j+1])[0..|s[0..j+1]|-1]) + (if (s[0..j+1])[|s[0..j+1]|-1] == '1' then 1 else 0));
  assert |s[0..j+1]| == j+1;
  assert j+1 != 0;
  assert Str2Int(s[0..j+1]) == 2 * Str2Int((s[0..j+1])[0..j]) + (if (s[0..j+1])[j] == '1' then 1 else 0);
  assert (s[0..j+1])[0..j] == s[0..j];
  assert (s[0..j+1])[j] == s[j];
  assert Str2Int(s[0..j+1]) == 2 * Str2Int(s[0..j]) + (if s[j] == '1' then 1 else 0);
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

  var p: nat := a * b;
  res := IntToBitString(p);
}
// </vc-code>

