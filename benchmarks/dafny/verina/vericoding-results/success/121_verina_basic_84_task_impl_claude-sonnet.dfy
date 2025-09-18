// <vc-preamble>
/* Helper function to process the replacement loop */
function ReplaceLoopSpec(oldArr: seq<int>, k: int, i: nat, acc: seq<int>): seq<int>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added correctness lemmas and properties to prove postconditions */
function ReplaceHelper(oldArr: seq<int>, k: int, i: nat, acc: seq<int>): seq<int>
    requires 0 <= i <= |oldArr|
    decreases |oldArr| - i
    ensures |ReplaceHelper(oldArr, k, i, acc)| == |acc| + |oldArr| - i
    ensures forall j :: 0 <= j < |acc| ==> ReplaceHelper(oldArr, k, i, acc)[j] == acc[j]
    ensures forall j :: i <= j < |oldArr| ==> 
        (oldArr[j] > k ==> ReplaceHelper(oldArr, k, i, acc)[|acc| + j - i] == -1) &&
        (oldArr[j] <= k ==> ReplaceHelper(oldArr, k, i, acc)[|acc| + j - i] == oldArr[j])
{
    if i == |oldArr| then acc
    else if oldArr[i] > k then ReplaceHelper(oldArr, k, i + 1, acc + [-1])
    else ReplaceHelper(oldArr, k, i + 1, acc + [oldArr[i]])
}

lemma ReplaceHelperCorrectness(oldArr: seq<int>, k: int)
    ensures |ReplaceHelper(oldArr, k, 0, [])| == |oldArr|
    ensures forall i :: 0 <= i < |oldArr| ==> 
        (oldArr[i] > k ==> ReplaceHelper(oldArr, k, 0, [])[i] == -1) &&
        (oldArr[i] <= k ==> ReplaceHelper(oldArr, k, 0, [])[i] == oldArr[i])
{
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
    /* code modified by LLM (iteration 4): added lemma call to establish postconditions */
    ReplaceHelperCorrectness(arr, k);
    result := ReplaceHelper(arr, k, 0, []);
}
// </vc-code>
