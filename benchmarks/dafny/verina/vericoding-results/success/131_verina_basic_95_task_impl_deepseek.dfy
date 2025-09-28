// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function swapFunc(arr: seq<int>, i: int, j: int): (result: seq<int>)
    requires 0 <= i < |arr|
    requires 0 <= j < |arr|
    ensures |result| == |arr|
    ensures result[i] == arr[j]
    ensures result[j] == arr[i]
    ensures forall k :: 0 <= k < |arr| && k != i && k != j ==> result[k] == arr[k]
{
    if i == j then
        arr
    else if i < j then
        arr[..i] + [arr[j]] + arr[i+1..j] + [arr[i]] + arr[j+1..]
    else
        arr[..j] + [arr[i]] + arr[j+1..i] + [arr[j]] + arr[i+1..]
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
    /* code modified by LLM (iteration 2): careful slicing for swap */
    result := swapFunc(arr, i, j);
}
// </vc-code>
