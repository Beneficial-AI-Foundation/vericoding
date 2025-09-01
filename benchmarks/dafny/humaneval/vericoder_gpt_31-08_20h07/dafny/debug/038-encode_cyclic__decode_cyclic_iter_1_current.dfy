method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultipleAfterSubtractingRemainder(n: int)
  ensures (n - n % 3) % 3 == 0
{
  var q := n / 3;
  var r := n % 3;
  assert n == 3 * q + r;
  assert 0 <= r < 3;
  assert n - r == 3 * q;
  assert (n - r) % 3 == 0;
}

lemma Plus2LtMWhenMod0(i: int, m: int)
  requires 0 <= i < m
  requires i % 3 == 0
  requires m % 3 == 0
  ensures i + 2 < m
{
  var k := i / 3;
  var t := m / 3;
  assert i == 3 * k + i % 3;
  assert m == 3 * t + m % 3;
  assert i == 3 * k;
  assert m == 3 * t;
  assert 3 * k < 3 * t;
  assert k < t;
  assert 3 * k + 2 < 3 * k + 3;
  assert 3 * k + 3 <= 3 * t;
}
// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var r := n % 3;
  var m := n - r;
  res := s;
  assert 0 <= r < 3;
  assert m <= n;
  MultipleAfterSubtractingRemainder(n);
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |res| == |s|
    invariant forall j :: 0 <= j < i && j % 3 == 0 ==> res[j] == s[j + 2]
    invariant forall j :: 0 <= j < i && j % 3 != 0 ==> res[j] == s[j - 1]
    invariant forall j :: i < j < |s| ==> res[j] == s[j]
    invariant forall j :: m <= j < |s| ==> res[j] == s[j]
  {
    if i % 3 == 0 {
      assert m % 3 == 0;
      Plus2LtMWhenMod0(i, m);
      assert i + 2 < m <= |s|;
      res := res[i := s[i + 2]];
    } else {
      assert i != 0;
      assert 1 <= i;
      res := res[i := s[i - 1]];
    }
    i := i + 1;
  }
}
// </vc-code>

