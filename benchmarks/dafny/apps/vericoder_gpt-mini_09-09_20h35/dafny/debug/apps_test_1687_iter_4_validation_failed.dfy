function min(a: seq<int>): int
    requires |a| > 0
    ensures min(a) in a
    ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0]
    else min(a[1..])
}

// <vc-helpers>
lemma IndexOfMin(a: seq<int>) returns (idx:int)
  requires |a| > 0
  ensures 0 <= idx < |a|
  ensures a[idx] == min(a)
{
  var j :| 0 <= j < |a| && a[j] == min(a);
  idx := j;
}

lemma ModLess(a:int, b:int)
  requires 0 <= a < b
  ensures a % b == a
{
  // a == b*(a/b) + a%b  and 0 <= a%b < b
  assert a == b * (a / b) + a % b;
  assert 0 <= a % b < b;
  var q := a / b;
  if q != 0 {
    // q >= 1, so q*b >= b > a
    assert q > 0;
    assert q * b >= b;
    assert q * b > a;
    // but q*b = a - (a % b) <= a, contradiction
    assert q * b <= a;
    assert false;
  }
  // thus q == 0, so a == a % b
  assert a % b == a;
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures result == -1 || result in a
    ensures result != -1 ==> forall i :: 0 <= i < |a| ==> a[i] % result == 0
    ensures result == -1 ==> forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
    ensures (forall i :: 0 <= i < |a| ==> a[i] % (min(a)) == 0) ==> result == min(a)
    ensures (exists i :: 0 <= i < |a| && a[i] % (min(a)) != 0) ==> result == -1
// </vc-spec>
// <vc-code>
{
  var m := min(a);
  var i := 0;
  var ok := true;
  var bad := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant ok ==> forall j :: 0 <= j < i ==> a[j] % m == 0
    invariant !ok ==> 0 <= bad < i && a[bad] % m != 0
    decreases |a| - i
  {
    if ok {
      if a[i] % m != 0 {
        ok := false;
        bad := i;
      }
    }
    i := i + 1;
  }

  if ok {
    result := m;
    // ok ensures divisibility for all indices
    assert forall j :: 0 <= j < |a| ==> a[j] % result == 0;
  } else {
    result := -1;
    var idxMin := IndexOfMin(a);
    assert 0 <= idxMin < |a|;
    assert a[idxMin] == m;
    assert 0 <= bad < |a|;
    assert a[bad] % m != 0;

    assert forall x | x in a ::
      exists i :: 0 <= i < |a| && a[i] % x != 0
    {
      fix x;
      assume x in a;
      if x == m {
        witness bad;
        assert 0 <= bad < |a|;
        assert a[bad] % x != 0;
      } else {
        // Show m < x, since m is minimum and x != m
        assert forall k :: 0 <= k < |a| ==> m <= a[k];
        var k :| 0 <= k < |a| && a[k] == x;
        assert m <= a[k];
        assert m <= x;
        assert m < x;

        // a[idxMin] == m and 0 < m < x, so a[idxMin] % x == a[idxMin] != 0
        assert 0 <= a[idxMin];
        assert a[idxMin] < x;
        ModLess(a[idxMin], x);
        assert a[idxMin] % x == a[idxMin];
        assert a[idxMin] != 0;
        witness idxMin;
        assert 0 <= idxMin < |a|;
      }
    }
  }
}
// </vc-code>

