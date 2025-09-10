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
function IndexOfMin(a: seq<int>): int
  requires |a| > 0
  decreases |a|
  ensures 0 <= result < |a|
  ensures a[result] == min(a)
{
  if |a| == 1 then 0
  else if a[0] == min(a) then 0
  else 1 + IndexOfMin(a[1..])
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
    assert forall j :: 0 <= j < |a| ==> a[j] % result == 0;
  } else {
    result := -1;
    var idxMin := IndexOfMin(a);
    assert 0 <= idxMin < |a|;
    assert a[idxMin] == m;
    assert 0 <= bad < |a|;
    assert a[bad] % m != 0;

    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      invariant forall k | 0 <= k < j :: exists i :: 0 <= i < |a| && a[i] % a[k] != 0
      decreases |a| - j
    {
      if a[j] == m {
        assert exists i :: i == bad && 0 <= i < |a| && a[i] % a[j] != 0;
      } else {
        assert m <= a[j];
        assert m != a[j];
        assert m < a[j];
        assert m > 0;
        assert m % a[j] != 0;
        assert exists i :: i == idxMin && 0 <= i < |a| && a[i] % a[j] != 0;
      }
      j := j + 1;
    }

    assert forall j :: 0 <= j < |a| ==> exists i :: 0 <= i < |a| && a[i] % a[j] != 0;
    assert forall x | x in a :: exists i :: 0 <= i < |a| && a[i] % x != 0;
  }
}
// </vc-code>

