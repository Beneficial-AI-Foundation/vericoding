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
        var mid := len / 2;
        var firstHalf := x[..mid];
        var secondHalf := x[mid..];
        
        // Assertions for recursive calls
        assert |firstHalf| > 0 by {
            if len == 1 {
                // This case goes to the 'isSorted' branch, so it satisfies.
                // We are in the 'else' branch, meaning not sorted, so len > 1.
                // If len > 1, then mid >= 1, so |firstHalf| >= 1.
            } else {
                // len > 1 implies mid >= 1.
                // If mid == 0, then len must be 1 (e.g., 1/2 = 0).
                // But len > 1 here since not sorted. So mid > 0 always.
                // Thus |firstHalf| = mid > 0.
            }
        }
        assert |secondHalf| > 0 by {
            // len - mid > 0.
            // If len is even, mid = len/2, len - mid = len/2, which is > 0 if len > 0.
            // If len is odd, mid = (len-1)/2, len - mid = len - (len-1)/2 = (2len - (len-1))/2 = (len+1)/2, which is > 0 if len > 0.
            // Since |x| > 0 is required, |secondHalf| > 0.
        }

        var leftResult := thanosSort(firstHalf);
        var rightResult := thanosSort(secondHalf);
        if leftResult > rightResult then leftResult else rightResult
}

predicate ValidInput(a: seq<int>)
{
    |a| > 0
}

predicate isSorted(x: seq<int>)
{
    forall i, j :: 0 <= i < j < |x| ==> x[i] <= x[j]
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

