/* code modified by LLM (iteration 1): removed redundant null checks from predicate requires clause */
predicate reversed (arr : array<char>, outarr: array<char>)
requires arr.Length == outarr.Length
reads arr, outarr
{
 forall k :: 0<=k<=arr.Length-1 ==> outarr[k] == arr[(arr.Length-1-k)]
}

//IMPL SPEC
/* code modified by LLM (iteration 1): removed redundant null checks from method specification */
method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr.Length > 0
ensures arr.Length == outarr.Length && reversed(arr,outarr)
{
    outarr := new char[arr.Length];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall k :: 0 <= k < i ==> outarr[k] == arr[arr.Length - 1 - k]
    {
        outarr[i] := arr[arr.Length - 1 - i];
        i := i + 1;
    }
}