// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simplified proofs to avoid forall-statements and rely on sortedness */
lemma SortedPrefixUpperBound(arr: array<int>, j: int)
  requires 0 <= j < arr.Length
  requires forall i, k :: 0 <= i < k < arr.Length ==> arr[i] <= arr[k]
  ensures forall i :: 0 <= i <= j ==> arr[i] <= arr[j]
{
  // Reflexivity helps for i == j; sortedness helps for i < j
  assert arr[j] <= arr[j];
}

/* helper modified by LLM (iteration 3): simplified proofs to avoid forall-statements and rely on sortedness */
lemma SortedSuffixLowerBound(arr: array<int>, j: int)
  requires 0 <= j < arr.Length
  requires forall i, k :: 0 <= i < k < arr.Length ==> arr[i] <= arr[k]
  ensures forall i :: j <= i < arr.Length ==> arr[j] <= arr[i]
{
  // Reflexivity helps for i == j; sortedness helps for j < i
  assert arr[j] <= arr[j];
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
  /* code modified by LLM (iteration 3): removed forall-statements to eliminate warnings; binary search with quantified asserts */
  var low := 0;
  var high := arr.Length;
  while low < high
    invariant 0 <= low <= high <= arr.Length
    invariant forall i :: 0 <= i < low ==> arr[i] <= elem
    invariant forall i :: high <= i < arr.Length ==> arr[i] > elem
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    if arr[mid] <= elem {
      SortedPrefixUpperBound(arr, mid);
      assert forall i :: 0 <= i <= mid ==> arr[i] <= arr[mid];
      assert arr[mid] <= elem;
      assert forall i :: 0 <= i <= mid ==> arr[i] <= elem;
      low := mid + 1;
    } else {
      SortedSuffixLowerBound(arr, mid);
      assert arr[mid] > elem;
      assert forall i :: mid <= i < arr.Length ==> arr[mid] <= arr[i];
      assert forall i :: mid <= i < arr.Length ==> arr[i] > elem;
      high := mid;
    }
  }
  assert low == high;
  if 0 < low {
    assert 0 < low <= arr.Length;
    assert 0 <= low - 1 < arr.Length;
    if arr[low - 1] == elem {
      result := low - 1;
      assert 0 <= result < arr.Length;
      assert result + 1 == low;
      assert low == high;
      assert forall k :: result < k < arr.Length ==> arr[k] != elem;
    } else {
      result := -1;
      assert 0 <= low - 1 < low;
      assert forall i :: 0 <= i < low ==> arr[i] <= elem;
      assert arr[low - 1] <= elem;
      assert arr[low - 1] != elem;
      assert arr[low - 1] < elem;
      SortedPrefixUpperBound(arr, low - 1);
      assert low == high;
      assert forall k :: 0 <= k < arr.Length ==> arr[k] != elem;
    }
  } else {
    result := -1;
    assert low == high;
    assert forall k :: 0 <= k < arr.Length ==> arr[k] != elem;
  }
}
// </vc-code>
