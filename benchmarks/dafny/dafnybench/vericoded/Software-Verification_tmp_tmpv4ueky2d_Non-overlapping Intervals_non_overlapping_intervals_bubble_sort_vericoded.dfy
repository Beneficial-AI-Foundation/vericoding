// Bubble Sort

// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1]
}

// <vc-helpers>
// No additional helper lemmas required for verification.
// </vc-helpers>

// <vc-spec>
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
// </vc-spec>
// <vc-code>
{
  var n := a.Length0;
  if n <= 1 {
    return;
  }
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant sorted(a, 0, i - 1)
    invariant forall k, k' :: 0 <= k <= i - 1 < k' < n ==> a[k, 1] <= a[k', 1]
  {
    // Find minimum element in a[i..n-1]
    var min := i;
    var j := i + 1;
    while j < n
      decreases n - j
      invariant i + 1 <= j <= n
      invariant i <= min < n
      invariant forall k :: i <= k < j ==> a[min, 1] <= a[k, 1]
    {
      if a[j, 1] < a[min, 1] {
        min := j;
      }
      j := j + 1;
    }
    // After inner loop, min is index of minimal element in [i..n-1]
    assert forall k :: i <= k < n ==> a[min, 1] <= a[k, 1];

    // From the partition invariant before swap, every element in prefix [0..i-1]
    // is <= every element in suffix [i..n-1]. In particular for k' = min we have:
    assert forall p :: 0 <= p < i ==> a[p, 1] <= a[min, 1];

    // Save old values of row at min for reasoning after swap
    var old_min0 := a[min, 0];
    var old_min1 := a[min, 1];

    // Swap entire rows i and min (both columns)
    if min != i {
      var tmp0 := a[i, 0];
      var tmp1 := a[i, 1];
      a[i, 0] := old_min0;
      a[i, 1] := old_min1;
      a[min, 0] := tmp0;
      a[min, 1] := tmp1;
    }

    // Now prove sorted(a, 0, i)
    // 1) For indices strictly below i, sorted(a,0,i-1) gives the ordering.
    // 2) For p < i, a[p,1] <= old_min1 (established above), and a[i,1] == old_min1 after swap,
    //    so a[p,1] <= a[i,1].
    assert forall p :: 0 <= p < i ==> a[p, 1] <= a[i, 1];
    assert sorted(a, 0, i);

    // Prove partitioned for new boundary i: forall k0 <= i < k1 ==> a[k0] <= a[k1]
    // First, prove a[i] <= every element in suffix
    assert forall k1 :: i < k1 < n ==> a[i, 1] <= a[k1, 1];
    // Next, prove every element in prefix [0..i-1] <= every element in suffix [i+1..n-1]
    assert forall k0, k1 ::
      0 <= k0 < i < k1 < n ==>
      a[k0, 1] <= a[k1, 1];

    i := i + 1;
  }

  // At end, i == n and sorted(a,0,n-1) holds by the loop invariant
}
// </vc-code>

