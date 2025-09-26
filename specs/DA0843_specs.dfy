// <vc-preamble>
predicate ValidTestCase(tc: (int, int, int, int, int))
{
    var (a, b, x, y, n) := tc;
    a >= x && b >= y && a >= 1 && b >= 1 && x >= 1 && y >= 1 && n >= 1 &&
    a <= 1000000000 && b <= 1000000000 && x <= 1000000000 && y <= 1000000000 && n <= 1000000000
}

function ComputeMinProduct(tc: (int, int, int, int, int)): int
    requires ValidTestCase(tc)
{
    var (a, b, x, y, n) := tc;
    var a1 := if a - n > x then a - n else x;
    var b1 := if b - (n - (a - a1)) > y then b - (n - (a - a1)) else y;
    var option1 := a1 * b1;
    var b2 := if b - n > y then b - n else y;
    var a2 := if a - (n - (b - b2)) > x then a - (n - (b - b2)) else x;
    var option2 := a2 * b2;
    if option1 < option2 then option1 else option2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(test_cases: seq<(int, int, int, int, int)>) returns (results: seq<int>)
    requires forall i :: 0 <= i < |test_cases| ==> ValidTestCase(test_cases[i])
    ensures |results| == |test_cases|
    ensures forall i :: 0 <= i < |results| ==> results[i] == ComputeMinProduct(test_cases[i])
// </vc-spec>
// <vc-code>
{
    results := [];
    for i := 0 to |test_cases|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == ComputeMinProduct(test_cases[j])
    {
        var (a, b, x, y, n) := test_cases[i];

        // Strategy 1: decrease a first, then b with remaining operations
        var a2 := if a - n > x then a - n else x;
        var b2 := if b - (n - (a - a2)) > y then b - (n - (a - a2)) else y;
        var option1 := a2 * b2;

        // Strategy 2: decrease b first, then a with remaining operations
        b2 := if b - n > y then b - n else y;
        a2 := if a - (n - (b - b2)) > x then a - (n - (b - b2)) else x;
        var option2 := a2 * b2;

        var min_product := if option1 < option2 then option1 else option2;
        results := results + [min_product];
    }
}
// </vc-code>
