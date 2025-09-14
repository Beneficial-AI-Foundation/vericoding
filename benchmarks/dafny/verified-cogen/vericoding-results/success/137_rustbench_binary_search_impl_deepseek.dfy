// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
function Contains(arr: array<int>, target: int, low: int, high: int): bool 
  requires 0 <= low <= high <= arr.Length
  reads arr
{
  exists i | low <= i < high :: arr[i] == target
}

lemma BinarySearchLemma(arr: array<int>, target: int, low: int, mid: int, high: int)
  requires 0 <= low <= mid < high <= arr.Length
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures Contains(arr, target, low, high) == (Contains(arr, target, low, mid) || Contains(arr, target, mid, high))
{
  /* helper modified by LLM (iteration 3): Fixed proof for binary search lemma */
  if Contains(arr, target, low, high) {
    var i :| low <= i < high && arr[i] == target;
    if i < mid {
      assert Contains(arr, target, low, mid);
    } else {
      assert Contains(arr, target, mid, high);
    }
  } else {
    assert forall i | low <= i < high :: arr[i] != target;
    assert !Contains(arr, target, low, mid);
    assert !Contains(arr, target, mid, high);
  }
}

lemma EmptyRangeNotContains(arr: array<int>, target: int, low: int)
  requires 0 <= low <= arr.Length
  ensures !Contains(arr, target, low, low)
{
  /* helper modified by LLM (iteration 3): Added proper precondition */
}

lemma FoundAtIndexImpliesContains(arr: array<int>, target: int, index: int, low: int, high: int)
  requires 0 <= low <= index < high <= arr.Length
  requires arr[index] == target
  ensures Contains(arr, target, low, high)
{
  /* helper modified by LLM (iteration 3): Kept trivial proof */
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(arr: array<int>, target: int) returns (result: Option<int>)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures match result {
        case Some(index) => 0 <= index < arr.Length && arr[index] == target
        case None => forall i :: 0 <= i < arr.Length ==> arr[i] != target
    }
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed loop invariant and assertions */
  var low := 0;
  var high := arr.Length;
  
  while low < high
    invariant 0 <= low <= high <= arr.Length
    invariant Contains(arr, target, 0, arr.Length) == Contains(arr, target, low, high)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    assert low <= mid < high;
    BinarySearchLemma(arr, target, low, mid, high);
    
    if arr[mid] == target {
      return Some(mid);
    } else if arr[mid] < target {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  EmptyRangeNotContains(arr, target, low);
  return None;
}
// </vc-code>
