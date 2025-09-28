// <vc-preamble>
/* Helper function to process the replacement loop */
function ReplaceLoopSpec(oldArr: seq<int>, k: int, i: nat, acc: seq<int>): seq<int>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Replace(arr: seq<int>, k: int) returns (result: seq<int>)
    ensures
        |result| == |arr| &&
        (forall i :: 0 <= i < |arr| ==> (arr[i] > k ==> result[i] == -1)) &&
        (forall i :: 0 <= i < |arr| ==> (arr[i] <= k ==> result[i] == arr[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implementing loop-based replacement */
  var i := 0;
  result := [];
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (arr[j] > k ==> result[j] == -1)
    invariant forall j :: 0 <= j < i ==> (arr[j] <= k ==> result[j] == arr[j])
  {
    if arr[i] > k {
      result := result + [-1];
    } else {
      result := result + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
