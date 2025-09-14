// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed invalid while loop from function and simplified */
function CountEvenNumbers(arr: seq<int>): int
{
    if |arr| == 0 then 0
    else (if IsEven(arr[|arr| - 1]) then 1 else 0) + CountEvenNumbers(arr[..|arr| - 1])
}

function CollectEvenNumbers(arr: array<int>, upTo: int): seq<int>
    reads arr
    requires 0 <= upTo <= arr.Length
{
    if upTo == 0 then []
    else 
        var rest := CollectEvenNumbers(arr, upTo - 1);
        if IsEven(arr[upTo - 1]) then rest + [arr[upTo - 1]] else rest
}

lemma CollectEvenNumbersProperties(arr: array<int>, upTo: int)
    requires 0 <= upTo <= arr.Length
    ensures forall x :: x in CollectEvenNumbers(arr, upTo) ==> IsEven(x) && x in arr[..upTo]
    ensures forall i :: 0 <= i < upTo && IsEven(arr[i]) ==> arr[i] in CollectEvenNumbers(arr, upTo)
{
    if upTo == 0 {
    } else {
        CollectEvenNumbersProperties(arr, upTo - 1);
    }
}

lemma OrderPreservationLemma(arr: array<int>)
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i <= j && IsEven(arr[i]) && IsEven(arr[j]) ==>
        exists ri, rj :: 0 <= ri < |CollectEvenNumbers(arr, arr.Length)| && 0 <= rj < |CollectEvenNumbers(arr, arr.Length)| &&
        ri <= rj && CollectEvenNumbers(arr, arr.Length)[ri] == arr[i] && CollectEvenNumbers(arr, arr.Length)[rj] == arr[j]
{
    var evenSeq := CollectEvenNumbers(arr, arr.Length);
    forall i, j | 0 <= i < arr.Length && 0 <= j < arr.Length && i <= j && IsEven(arr[i]) && IsEven(arr[j])
        ensures exists ri, rj :: 0 <= ri < |evenSeq| && 0 <= rj < |evenSeq| &&
            ri <= rj && evenSeq[ri] == arr[i] && evenSeq[rj] == arr[j]
    {
        var ri := FindIndexInCollected(arr, arr.Length, i);
        var rj := FindIndexInCollected(arr, arr.Length, j);
        assert ri <= rj;
    }
}

function FindIndexInCollected(arr: array<int>, upTo: int, target: int): int
    reads arr
    requires 0 <= target < upTo <= arr.Length
    requires IsEven(arr[target])
    ensures 0 <= FindIndexInCollected(arr, upTo, target) < |CollectEvenNumbers(arr, upTo)|
    ensures CollectEvenNumbers(arr, upTo)[FindIndexInCollected(arr, upTo, target)] == arr[target]
{
    if target == 0 then
        if IsEven(arr[0]) then 0 else 0
    else
        var prevCount := if IsEven(arr[target]) then 1 else 0;
        prevCount + FindIndexInCollected(arr, target, target - 1)
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
    /* code modified by LLM (iteration 5): fixed compilation error and maintained ordering proof */
    var evenSeq := CollectEvenNumbers(arr, arr.Length);
    CollectEvenNumbersProperties(arr, arr.Length);
    OrderPreservationLemma(arr);
    
    result := new int[|evenSeq|];
    
    var i := 0;
    while i < |evenSeq|
        invariant 0 <= i <= |evenSeq|
        invariant result.Length == |evenSeq|
        invariant forall j :: 0 <= j < i ==> result[j] == evenSeq[j]
    {
        result[i] := evenSeq[i];
        i := i + 1;
    }
}
// </vc-code>
