// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove monotonicity between indices */
lemma SortedMonotone(arr: array<int>, i: int, j: int)
  requires 0 <= i <= j < arr.Length
  requires forall p, q :: 0 <= p < q < arr.Length ==> arr[p] <= arr[q]
{
  if i < j {
    assert arr[i] <= arr[j];
  }
}

/* helper modified by LLM (iteration 2): elements left of mid are <= elem */
lemma LeftLeqElem(arr: array<int>, mid: int, elem: int, k: int)
  requires 0 <= k < mid < arr.Length
  requires forall p, q :: 0 <= p < q < arr.Length ==> arr[p] <= arr[q]
  requires arr[mid] <= elem
{
  SortedMonotone(arr, k, mid);
  assert arr[k] <= arr[mid];
  assert arr[mid] <= elem;
  assert arr[k] <= elem;
}

/* helper modified by LLM (iteration 2): elements right of mid are > elem */
lemma RightGtElem(arr: array<int>, mid: int, elem: int, k: int)
  requires 0 <= mid < k < arr.Length
  requires forall p, q :: 0 <= p < q < arr.Length ==> arr[p] <= arr[q]
  requires arr[mid] > elem
{
  SortedMonotone(arr, mid, k);
  if mid < k {
    assert arr[mid] <= arr[k];
  }
  assert arr[mid] > elem;
  assert arr[k] > elem;
}

// </vc-helpers>

// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures
        (result >= 0 ==> 
            0 <= result < arr.Length &&
            arr[result] == elem &&
            forall k :: result < k < arr.Length ==> arr[k] != elem) &&
        (result == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != elem)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): binary search to find last index with value <= elem, then set result accordingly */
  var low := 0;
  var high := arr.Length - 1;
  result := -1;
  while low <= high
    invariant 0 <= low <= arr.Length
    invariant -1 <= high < arr.Length
    invariant low <= high + 1
    invariant forall k :: 0 <= k < low ==> arr[k] <= elem
    invariant forall k :: high < k < arr.Length ==> arr[k] > elem
    decreases high - low + 1
  {
    var mid := low + (high - low) / 2;
    if arr[mid] <= elem {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  if high >= 0 && arr[high] == elem {
    result := high;
  } else {
    result := -1;
  }
}

// </vc-code>
