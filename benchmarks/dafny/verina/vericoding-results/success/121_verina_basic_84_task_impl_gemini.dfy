// <vc-preamble>
/* Helper function to process the replacement loop */
function ReplaceLoopSpec(oldArr: seq<int>, k: int, i: nat, acc: seq<int>): seq<int>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added requires clause to prevent index out of range error. */
predicate IsPartialResult(arr: seq<int>, k: int, i: nat, res: seq<int>)
    requires i <= |arr|
{
    |res| == i &&
    forall j :: 0 <= j < i ==> res[j] == (if arr[j] > k then -1 else arr[j])
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
    /* code modified by LLM (iteration 2): No logical changes needed in the method body. */
    var res: seq<int> := [];
    var i: nat := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant IsPartialResult(arr, k, i, res)
    {
        var next_val := if arr[i] > k then -1 else arr[i];
        res := res + [next_val];
        i := i + 1;
    }
    result := res;
}
// </vc-code>
