// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): switched to 'function' and provided pure swap via slicing */
function SwapSeq(arr: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < |arr|
  requires 0 <= j < |arr|
{
  if i == j then arr
  else if i < j then arr[..i] + [arr[j]] + arr[i+1..j] + [arr[i]] + arr[j+1..]
  else arr[..j] + [arr[i]] + arr[j+1..i] + [arr[j]] + arr[i+1..]
}
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
  /* code modified by LLM (iteration 2): implement swapping via sequence slicing */
  if i == j {
    result := arr;
  } else if i < j {
    result := arr[..i] + [arr[j]] + arr[i+1..j] + [arr[i]] + arr[j+1..];
  } else {
    result := arr[..j] + [arr[i]] + arr[j+1..i] + [arr[j]] + arr[i+1..];
  }
}
// </vc-code>
