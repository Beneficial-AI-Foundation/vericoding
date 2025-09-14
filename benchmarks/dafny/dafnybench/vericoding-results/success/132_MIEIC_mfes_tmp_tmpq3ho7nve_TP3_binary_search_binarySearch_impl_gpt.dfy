// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found.

// Simple test cases to check the post-condition.

/*
a) Identify adequate pre and post-conditions for this method, 
and encode them as “requires” and “ensures” clauses in Dafny. 
You can use the predicate below if needed.

b) Identify an adequate loop variant and loop invariant, and encode them 
as “decreases” and “invariant” clauses in Dafny.
*/

// <vc-helpers>
lemma sorted_prefix_lt_implies_all_lt(a: array<int>, mid: int, x: int)
  requires isSorted(a)
  requires 0 <= mid < a.Length
  requires a[mid] < x
  ensures forall i :: 0 <= i <= mid ==> a[i] < x
{
  forall i | 0 <= i <= mid
    ensures a[i] < x
  {
    if i < mid {
      assert 0 <= i < mid < a.Length;
      assert a[i] <= a[mid];
      assert a[i] < x;
    } else {
      assert i == mid;
      assert a[i] < x;
    }
  }
}

lemma sorted_suffix_gt_implies_all_gt(a: array<int>, mid: int, x: int)
  requires isSorted(a)
  requires 0 <= mid < a.Length
  requires a[mid] > x
  ensures forall i :: mid <= i < a.Length ==> a[i] > x
{
  forall i | mid <= i < a.Length
    ensures a[i] > x
  {
    if i > mid {
      assert 0 <= mid < i < a.Length;
      assert a[mid] <= a[i];
      assert a[i] > x;
    } else {
      assert i == mid;
      assert a[i] > x;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method binarySearch(a: array<int>, x: int) returns (index: int) 
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures if index != -1 then a[index] == x 
        else x !in a[..] //forall i :: 0 <= i < a.Length ==> a[i] != x
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] != x
    invariant forall i :: hi <= i < a.Length ==> a[i] != x
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    assert lo <= mid < hi;
    if a[mid] == x {
      return mid;
    } else if a[mid] < x {
      sorted_prefix_lt_implies_all_lt(a, mid, x);
      lo := mid + 1;
    } else {
      sorted_suffix_gt_implies_all_gt(a, mid, x);
      hi := mid;
    }
  }

  assert lo >= hi;
  assert lo == hi;

  forall i | 0 <= i < a.Length
    ensures a[i] != x
  {
    if i < lo {
      assert a[i] != x;
    } else {
      assert hi <= i < a.Length;
      assert a[i] != x;
    }
  }

  return -1;
}
// </vc-code>

