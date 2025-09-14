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
lemma NotSortedImpliesLength(x: seq<int>)
    requires !isSorted(x)
    ensures |x| >= 2
{
    if |x| < 2 {
        assert isSorted(x);
    }
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
    if isSorted(a) {
        result := |a|;
    } else {
        NotSortedImpliesLength(a);
        var mid := |a|/2;
        var firstHalf := a[..mid];
        var secondHalf := a[mid..];

        var leftResult := solve(firstHalf);
        var rightResult := solve(secondHalf);

        if leftResult > rightResult {
            result := leftResult;
        } else {
            result := rightResult;
        }
    }
}
// </vc-code>

