// <vc-preamble>
/* Helper function to process the replacement loop */
function ReplaceLoopSpec(oldArr: seq<int>, k: int, i: nat, acc: seq<int>): seq<int>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): compute replacement sequence iteratively */
function ReplaceLoopCompute(oldArr: seq<int>, k: int, i: nat, acc: seq<int>): seq<int>
  decreases |oldArr| - i
{
  if i >= |oldArr| then acc else ReplaceLoopCompute(oldArr, k, i + 1, acc + [if oldArr[i] > k then -1 else oldArr[i]])
}
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
  /* code modified by LLM (iteration 2): iterative array construction */
  var n := |arr|;
  var a := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> (arr[j] > k ==> a[j] == -1) && (arr[j] <= k ==> a[j] == arr[j])
    decreases n - i
  {
    if arr[i] > k {
      a[i] := -1;
    } else {
      a[i] := arr[i];
    }
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
