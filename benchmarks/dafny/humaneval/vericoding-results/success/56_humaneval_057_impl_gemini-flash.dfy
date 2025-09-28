// <vc-preamble>

function monotonic(l: seq<int>): bool
    ensures |l| <= 1 ==> monotonic(l) == true
    ensures |l| > 1 ==> (monotonic(l) == (
        (forall i :: 0 <= i < |l| - 1 ==> l[i] <= l[i + 1]) ||
        (forall i :: 0 <= i < |l| - 1 ==> l[i] >= l[i + 1])
    ))
{
    if |l| <= 1 then true
    else
        var increasing := forall i :: 0 <= i < |l| - 1 ==> l[i] <= l[i + 1];
        var decreasing := forall i :: 0 <= i < |l| - 1 ==> l[i] >= l[i + 1];
        increasing || decreasing
}
// </vc-preamble>

// <vc-helpers>
function isIncreasing(l: seq<int>): bool
    ensures isIncreasing(l) == (forall i :: 0 <= i < |l| - 1 ==> l[i] <= l[i + 1])
{
    forall i :: 0 <= i < |l| - 1 ==> l[i] <= l[i + 1]
}

function isDecreasing(l: seq<int>): bool
    ensures isDecreasing(l) == (forall i :: 0 <= i < |l| - 1 ==> l[i] >= l[i + 1])
{
    forall i :: 0 <= i < |l| - 1 ==> l[i] >= l[i + 1]
}
// </vc-helpers>

// <vc-spec>
method IsMonotonic(l: seq<int>) returns (result: bool)
    ensures result == monotonic(l)
// </vc-spec>
// <vc-code>
{
    if |l| <= 1 {
        result := true;
    } else {
        var increasing := isIncreasing(l);
        var decreasing := isDecreasing(l);
        result := increasing || decreasing;
    }
}
// </vc-code>
