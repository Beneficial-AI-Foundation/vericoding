//IMPL contains
/* code modified by LLM (iteration 4): fixed function declaration syntax */
function contains(arr: seq<int>, key: int): bool
    ensures contains(arr, key) == (exists i :: 0 <= i < |arr| && arr[i] == key)
{
    if |arr| == 0 then false
    else if arr[0] == key then true
    else contains(arr[1..], key)
}

//IMPL intersection
/* code modified by LLM (iteration 4): implemented intersection method with proper loop invariants */
method intersection(arr1: seq<int>, arr2: seq<int>) returns (result: seq<int>)
    ensures forall i :: 0 <= i < |result| ==> (result[i] in arr1 && result[i] in arr2)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    result := [];
    var idx := 0;
    
    while idx < |arr1|
        invariant 0 <= idx <= |arr1|
        invariant forall k :: 0 <= k < |result| ==> (result[k] in arr1 && result[k] in arr2)
        invariant forall k1, k2 :: 0 <= k1 < k2 < |result| ==> result[k1] != result[k2]
    {
        var elem := arr1[idx];
        if contains(arr2, elem) && !contains(result, elem) {
            result := result + [elem];
        }
        idx := idx + 1;
    }
}