// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no change, was correct */
function Max(a: int, b: int): int {
    if a > b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires ValidInput(a)
    ensures result == thanosSort(a)
    ensures 1 <= result <= |a|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): corrected missing brace in the `if` statement for verification. */
{
    var len := |a|;
    if isSorted(a) {
        result := len;
    } else {
        var firstHalf := a[..len/2];
        var secondHalf := a[len/2..];
        var leftResult: int;
        var rightResult: int;

        leftResult := thanosSort(firstHalf);
        rightResult := thanosSort(secondHalf);
     
        result := Max(leftResult, rightResult);
    }
}
// </vc-code>
