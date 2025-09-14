predicate ValidInput(a: seq<int>)
{
    |a| > 0
}

predicate isSorted(x: seq<int>)
{
    forall i, j :: 0 <= i < j < |x| ==> x[i] <= x[j]
}

function thanosSort(x: seq<int>): int
    requires |x| > 0
    ensures thanosSort(x) >= 1
    ensures thanosSort(x) <= |x|
    ensures isSorted(x) ==> thanosSort(x) == |x|
{
    var len := |x|;
    if isSorted(x) then
        len
    else
        var firstHalf := x[..len/2];
        var secondHalf := x[len/2..];
        var leftResult := thanosSort(firstHalf);
        var rightResult := thanosSort(secondHalf);
        if leftResult > rightResult then leftResult else rightResult
}

// <vc-helpers>
lemma ThanosSort_Bounds(x: seq<int>)
    requires |x| > 0
    ensures 1 <= thanosSort(x) <= |x|
{
    // This follows from the postconditions of thanosSort
}

lemma ThanosSort_Preserves_Sorted(x: seq<int>)
    requires |x| > 0
    requires isSorted(x)
    ensures thanosSort(x) == |x|
{
    // This follows from the postconditions of thanosSort
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires ValidInput(a)
    ensures result == thanosSort(a)
    ensures 1 <= result <= |a|
// </vc-spec>
// <vc-code>
{
    result := thanosSort(a);
}
// </vc-code>

