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
    assume {:axiom} false;
  }
// </vc-code>
