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
  /* code modified by LLM (iteration 3): Fix syntax errors by removing invalid ':p', correct the while loop implementation with proper invariants and decreases clause for full verification */
  var resultSeq := [];
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |resultSeq| == i
    invariant forall j :: 0 <= j < i ==> (arr[j] > k ==> resultSeq[j] == -1) && (arr[j] <= k ==> resultSeq[j] == arr[j])
    decreases |arr| - i
  {
    if arr[i] > k {
      resultSeq := resultSeq + [-1];
    } else {
      resultSeq := resultSeq + [arr[i]];
    }
    i := i + 1;
  }
  result := resultSeq;
}
// </vc-code>
