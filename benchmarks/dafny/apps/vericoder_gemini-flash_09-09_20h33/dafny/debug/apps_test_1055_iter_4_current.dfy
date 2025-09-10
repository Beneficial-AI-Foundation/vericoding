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
// It seems the original structure mistakenly duplicated thanosSort, ValidInput, and isSorted in helpers.
// The correct approach is to define them once, typically outside helpers,
// and reference them as needed. Since they were already provided in the preamble,
// their re-definition here caused "Duplicate member name" errors.
// Removing the redundant definitions from helpers resolves these errors.

// No helper functions are needed for this specific verification task,
// as the `thanosSort`, `ValidInput`, and `isSorted` functions/predicates
// are already defined in the pre-amble.
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

