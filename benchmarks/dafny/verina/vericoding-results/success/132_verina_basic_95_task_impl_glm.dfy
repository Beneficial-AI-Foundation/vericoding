// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method swap(arr: seq<int>, i: int, j: int) returns (result: seq<int>)
    requires 0 <= i < |arr|
    requires 0 <= j < |arr|
    ensures |result| == |arr|
    ensures result[i] == arr[j]
    ensures result[j] == arr[i]
    ensures forall k :: 0 <= k < |arr| && k != i && k != j ==> result[k] == arr[k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): replaced sequence comprehension with sequence update to avoid index out of range */
  result := arr[i := arr[j]][j := arr[i]];
}
// </vc-code>
