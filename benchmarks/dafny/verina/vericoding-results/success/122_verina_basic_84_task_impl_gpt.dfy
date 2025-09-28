// <vc-preamble>
/* Helper function to process the replacement loop */
function ReplaceLoopSpec(oldArr: seq<int>, k: int, i: nat, acc: seq<int>): seq<int>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple value replacement based on threshold k */
function ReplaceValue(x: int, k: int): int {
  if x > k then -1 else x
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
  /* code modified by LLM (iteration 2): implement executable loop with sequence updates instead of comprehension */
  var res := arr;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |res| == |arr|
    invariant forall j :: 0 <= j < i ==> (arr[j] > k ==> res[j] == -1)
    invariant forall j :: 0 <= j < i ==> (arr[j] <= k ==> res[j] == arr[j])
    invariant forall j :: i <= j < |arr| ==> res[j] == arr[j]
  {
    if arr[i] > k {
      res := res[i := -1];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>
