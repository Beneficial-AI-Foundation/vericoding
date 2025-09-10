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
lemma ThanosSortBounds(x: seq<int>)
    requires |x| > 0
    ensures 1 <= thanosSort(x) <= |x|
{
    // This follows from the ensures clauses of thanosSort function
}

lemma ThanosSortCorrectness(x: seq<int>)
    requires |x| > 0
    ensures isSorted(x) ==> thanosSort(x) == |x|
{
    // This follows from the ensures clauses of thanosSort function
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
    var len := |a|;
    if isSorted(a) {
        result := len;
    } else {
        var firstHalf := a[..len/2];
        var secondHalf := a[len/2..];
        
        assert |firstHalf| > 0;
        assert |secondHalf| > 0;
        
        var leftResult := solve(firstHalf);
        var rightResult := solve(secondHalf);
        
        assert leftResult == thanosSort(firstHalf);
        assert rightResult == thanosSort(secondHalf);
        
        if leftResult > rightResult {
            result := leftResult;
        } else {
            result := rightResult;
        }
    }
}
// </vc-code>

