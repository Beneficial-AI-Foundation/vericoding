predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}

// <vc-helpers>
lemma SwapPreservesMultiset(a: array<int>, i: int, j: int)
  requires a != null
  requires 0 <= i < j < a.Length
  ensures multiset(old(a[..])) == multiset(a[..])
{
  var old_slice := old(a[..]);
  var new_slice := a[..];
  assert multiset(old_slice) == multiset(new_slice) by {
    assert forall x | x in multiset(old_slice) :: x in multiset(new_slice);
    assert forall x | x in multiset(new_slice) :: x in multiset(old_slice);
  }
}

lemma BubblePassHelper(a: array<int>, j: int, n: int, i: int)
  requires a != null
  requires 0 <= i < n <= a.Length
  requires 0 <= j < n - i - 1
  requires forall k :: 0 <= k <= j ==> a[k] <= a[j]
  ensures forall k :: 0 <= k <= j + 1 ==> a[k] <= a[j + 1]
{
  if j + 1 < n - i - 1 {
    // Prove that a[j+1] is >= all elements from 0 to j
    forall k | 0 <= k <= j + 1
      ensures a[k] <= a[j + 1]
    {
      if k <= j {
        // From the precondition, we know a[k] ≤ a[j]
        // We need to show a[j] ≤ a[j+1] to conclude a[k] ≤ a[j+1]
        assert a[k] <= a[j];
        // This requires comparing a[j] and a[j+1] - may need additional context
      }
    }
  }
}

lemma BubbleSortLoopHelper(a: array<int>, i: nat, n: nat)
  requires a != null
  requires 0 <= i <= n <= a.Length
  requires sorted_between(a, n - i, n)
  requires forall k :: 0 <= k < n - i ==> a[k] <= a[n - i - 1]
  ensures sorted_between(a, n - i - 1, n)
{
  // Extend the sorted region to include the element at position n-i-1
  assert forall x, y :: n - i - 1 <= x < y < n ==> a[x] <= a[y] by {
    if x == n - i - 1 && y >= n - i {
      assert a[x] <= a[y] from forall k :: 0 <= k < n - i ==> a[k] <= a[n - i - 1];
    } else if x >= n - i {
      assert a[x] <= a[y] from sorted_between(a, n - i, n);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant sorted_between(a, n - i, n)
    invariant multiset(old(a[..])) == multiset(a[..])
    decreases n - i
  {
    var j := 0;
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
      invariant sorted_between(a, n - i, n)
      invariant multiset(old(a[..])) == multiset(a[..])
      decreases n - i - 1 - j
    {
      if a[j] > a[j + 1] {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
        SwapPreservesMultiset(a, j, j+1);
      } else {
        // Maintain the invariant when no swap occurs
        assert forall k :: 0 <= k <= j ==> a[k] <= a[j];
      }
      // Update the invariant to include j+1
      assert forall k :: 0 <= k <= j + 1 ==> a[k] <= a[j + 1] by {
        BubblePassHelper(a, j, n, i);
      }
      j := j + 1;
    }
    // After the inner loop, the element at position n-i-1 is the largest in the unsorted part
    assert forall k :: 0 <= k < n - i ==> a[k] <= a[n - i - 1];
    BubbleSortLoopHelper(a, i, n);
    i := i + 1;
  }
}
// </vc-code>

