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
        var increasing := true;
        var decreasing := true;
        var i := 0;
        while i < |l| - 1
            invariant 0 <= i <= |l| - 1
            invariant increasing == (forall j :: 0 <= j < i ==> l[j] <= l[j + 1])
            invariant decreasing == (forall j :: 0 <= j < i ==> l[j] >= l[j + 1])
        {
            if l[i] > l[i + 1] {
                increasing := false;
            }
            if l[i] < l[i + 1] {
                decreasing := false;
            }
            i := i + 1;
        }
        result := increasing || decreasing;
    }
}
// </vc-code>
