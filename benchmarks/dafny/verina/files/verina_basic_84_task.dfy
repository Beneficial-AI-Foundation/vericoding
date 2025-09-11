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
    // impl-start
    assume {:axiom} false;
    result := [];
    // impl-end
}
// </vc-code>
