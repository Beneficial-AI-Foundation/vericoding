predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && k >= 1 && |a| == n &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 1) &&
    (exists i :: 0 <= i < |a| && k % a[i] == 0)
}

predicate ValidBucket(k: int, bucketSize: int)
{
    bucketSize >= 1 && k % bucketSize == 0
}

function HoursNeeded(k: int, bucketSize: int): int
    requires ValidBucket(k, bucketSize)
{
    k / bucketSize
}

predicate IsOptimalChoice(k: int, a: seq<int>, chosenBucket: int)
{
    0 <= chosenBucket < |a| &&
    ValidBucket(k, a[chosenBucket]) &&
    (forall i :: 0 <= i < |a| && ValidBucket(k, a[i]) ==> a[i] <= a[chosenBucket])
}

// <vc-helpers>
lemma HoursNeededAtLeast1(k: int, bucket: int)
  requires k >= 1 && ValidBucket(k, bucket)
  ensures HoursNeeded(k, bucket) >= 1
{
  var q := k / bucket;
  // since bucket divides k, k == bucket * q
  assert k == bucket * q;
  if q == 0 {
    // then k == 0, contradicting k >= 1
    assert k == 0;
    assert false;
  }
  assert q >= 1;
  assert HoursNeeded(k, bucket) == q;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, k, a)
    ensures result >= 1
    ensures exists i :: IsOptimalChoice(k, a, i) && result == HoursNeeded(k, a[i])
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  while idx < |a| && k % a[idx] != 0
    decreases |a| - idx
    invariant 0 <= idx <= |a|
    invariant forall t :: 0 <= t < idx ==> k % a[t] != 0
  {
    idx := idx + 1;
  }
  if idx == |a| {
    var j :| 0 <= j < |a| && k % a[j] == 0;
    // from the loop invariant we know for all t < idx (i.e., all t < |a|) k % a[t] != 0,
    // which contradicts the existence of such j
    assert forall t :: 0 <= t < idx ==> k % a[t] != 0;
    assert k % a[j] != 0;
    assert k % a[j] == 0;
    assert false;
  }

  var chosen := idx;
  var i := idx + 1;
  while i < |a|
    decreases |a| - i
    invariant 0 <= chosen < |a|
    invariant k % a[chosen] == 0
    invariant forall t :: 0 <= t < i && k % a[t] == 0 ==> a[t] <= a[chosen]
  {
    if k % a[i] == 0 && a[i] > a[chosen] {
      chosen := i;
    }
    i := i + 1;
  }

  // chosen is an optimal index; set result accordingly
  result := HoursNeeded(k, a[chosen]);
  // prove result >= 1 using lemma (ValidInput ensures a[chosen] >= 1)
  HoursNeededAtLeast1(k, a[chosen]);
}
// </vc-code>

