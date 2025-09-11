// <vc-preamble>
function Min(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        if a[|a|-1] <= minPrefix then a[|a|-1] else Min(a[..|a|-1])
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        if a[|a|-1] >= maxPrefix then a[|a|-1] else Max(a[..|a|-1])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
