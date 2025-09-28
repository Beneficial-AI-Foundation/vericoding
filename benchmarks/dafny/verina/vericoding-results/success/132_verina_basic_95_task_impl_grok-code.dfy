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
/* code modified by LLM (iteration 2): add condition for i==j to handle slice bounds and satisfy ensures */
{
  var min_idx := if i < j then i else j;
  var max_idx := if i < j then j else i;
  if min_idx == max_idx {
    result := arr;
  } else {
    result := arr[..min_idx] + [arr[max_idx]] + arr[min_idx+1..max_idx] + [arr[min_idx]] + arr[max_idx+1..];
  }
}
// </vc-code>
