// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): propagate less-than to lower indices */
lemma LessProp(arr: array<int>, target: int, i: int)
  requires 0 <= i < arr.Length
  requires forall p, q :: 0 <= p < q < arr.Length ==> arr[p] <= arr[q]
  requires arr[i] < target
  ensures forall k {:trigger arr[k]} :: 0 <= k <= i ==> arr[k] < target
  decreases i
{
  if i == 0 {
    assert arr[0] < target;
  } else {
    LessProp(arr, target, i - 1);
  }
  assert forall k {:trigger arr[k]} :: 0 <= k <= i ==> arr[k] < target;
}

/* helper modified by LLM (iteration 4): propagate >= to higher indices */
lemma GreaterProp(arr: array<int>, target: int, i: int)
  requires 0 <= i < arr.Length
  requires forall p, q :: 0 <= p < q < arr.Length ==> arr[p] <= arr[q]
  requires arr[i] >= target
  ensures forall k {:trigger arr[k]} :: i <= k < arr.Length ==> arr[k] >= target
  decreases arr.Length - i
{
  if i == arr.Length - 1 {
    assert arr[i] >= target;
  } else {
    GreaterProp(arr, target, i + 1);
  }
  assert forall k {:trigger arr[k]} :: i <= k < arr.Length ==> arr[k] >= target;
}

// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures (result >= 0 ==> (
        0 <= result < arr.Length &&
        arr[result] == target &&
        forall i :: 0 <= i < result ==> arr[i] != target
    )) &&
    (result == -1 ==> (
        forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): binary search for first occurrence using helpers */
  var lo := 0;
  var hi := arr.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= arr.Length
    invariant forall k :: 0 <= k < lo ==> arr[k] < target
    invariant forall k :: hi <= k < arr.Length ==> arr[k] >= target
  {
    var mid := lo + (hi - lo) / 2;
    if arr[mid] < target {
      LessProp(arr, target, mid);
      lo := mid + 1;
    } else {
      GreaterProp(arr, target, mid);
      hi := mid;
    }
  }
  if lo < arr.Length && arr[lo] == target {
    result := lo;
  } else {
    result := -1;
  }
}

// </vc-code>
