

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var a := new int[|l|];
  var k := 0;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant 0 <= k <= |l|
    invariant k <= i
    invariant forall j :: 0 <= j < i && l[j] > 0 ==> exists t :: 0 <= t < k && a[t] == l[j]
    invariant forall t :: 0 <= t < k ==> a[t] > 0 && exists j :: 0 <= j < i && a[t] == l[j]
  {
    var cur := i;
    if l[cur] > 0 {
      a[k] := l[cur];
      k := k + 1;
      assert a[k-1] == l[cur];
      assert 0 <= k-1 < k;
    }
    i := i + 1;
    if l[cur] > 0 {
      assert exists t :: 0 <= t < k && a[t] == l[cur];
      assert a[k-1] > 0;
      assert exists jj :: 0 <= jj < i && a[k-1] == l[jj];
    }
    // Help the verifier by re-establishing the quantified invariants explicitly
    assert forall j :: 0 <= j < i && l[j] > 0 ==> exists t :: 0 <= t < k && a[t] == l[j];
    assert forall t :: 0 <= t < k ==> a[t] > 0 && exists j :: 0 <= j < i && a[t] == l[j];
  }
  result := a[..k];
}
// </vc-code>

