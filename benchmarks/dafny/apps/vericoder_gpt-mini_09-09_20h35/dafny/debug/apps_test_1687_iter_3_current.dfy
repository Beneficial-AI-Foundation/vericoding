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
  var i := 0;
  while i < |a|
    decreases |a| - i
  {
    if a[i] == min(a) {
      idx := i;
      return;
    }
    i := i + 1;
  }
  // By ensures of min, this is unreachable
  assert false;
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
    // Prove: for every x in a there exists an index i with a[i] % x != 0
    var idxMin := IndexOfMin(a);
    assert 0 <= idxMin < |a|;
    assert a[idxMin] == m;
    assert 0 <= bad < |a|;
    assert a[bad] % m != 0;
    // For any x in a, choose witness: if x == m use bad, else use idxMin.
    assert forall x | x in a ::
      exists i ::
        if x == m then i == bad && 0 <= i < |a| && a[i] % x != 0
        else i == idxMin && 0 <= i < |a| && a[i] % x != 0;
  }
}
// </vc-code>

