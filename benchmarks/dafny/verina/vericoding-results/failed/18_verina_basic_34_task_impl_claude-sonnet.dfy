// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified approach without complex helpers */
lemma SequenceContains<T>(s: seq<T>, x: T, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires x in s[start..end]
    ensures x in s
{
    // follows from subsequence containment
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (result: array<int>)
    ensures forall x :: x in result[..] ==> IsEven(x) && x in arr[..]
    ensures forall x :: x in arr[..] && IsEven(x) ==> x in result[..]
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i <= j 
        && IsEven(arr[i]) && IsEven(arr[j]) ==> 
        exists ri, rj :: 0 <= ri < result.Length && 0 <= rj < result.Length 
            && ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation without complex invariants */
    var evenIndices: seq<int> := [];
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall k :: 0 <= k < |evenIndices| ==> 0 <= evenIndices[k] < i
        invariant forall k :: 0 <= k < |evenIndices| ==> IsEven(arr[evenIndices[k]])
        invariant forall j :: 0 <= j < i && IsEven(arr[j]) ==> j in evenIndices
        invariant forall k1, k2 :: 0 <= k1 < k2 < |evenIndices| ==> evenIndices[k1] < evenIndices[k2]
    {
        if IsEven(arr[i]) {
            evenIndices := evenIndices + [i];
        }
        i := i + 1;
    }
    
    result := new int[|evenIndices|];
    i := 0;
    
    while i < |evenIndices|
        invariant 0 <= i <= |evenIndices|
        invariant forall k :: 0 <= k < i ==> result[k] == arr[evenIndices[k]]
    {
        result[i] := arr[evenIndices[i]];
        i := i + 1;
    }
}
// </vc-code>
