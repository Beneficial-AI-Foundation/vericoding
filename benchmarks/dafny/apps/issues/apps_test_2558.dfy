// <vc-preamble>
predicate ValidInput(testCase: (int, int, int, int))
{
    var (a, b, c, d) := testCase;
    a >= 0 && b >= 0 && c >= 0 && d >= 0
}

predicate ValidTestCases(testCases: seq<(int, int, int, int)>)
{
    |testCases| >= 0 && forall i :: 0 <= i < |testCases| ==> ValidInput(testCases[i])
}

predicate ValidResults(testCases: seq<(int, int, int, int)>, results: seq<int>)
{
    |results| == |testCases| &&
    forall i :: 0 <= i < |testCases| ==> 
        var (a, b, c, d) := testCases[i];
        (a - b * c > 0 ==> results[i] == -1) &&
        (a - b * c <= 0 && d >= c ==> results[i] == a) &&
        (a - b * c <= 0 && d < c ==> results[i] >= 0) &&
        results[i] >= -1
}

function getSm(k: int, a: int, b: int, c: int, d: int): int
    requires a >= 0 && b >= 0 && c >= 0 && d >= 0 && k >= 0
    ensures getSm(k, a, b, c, d) == (k + 1) * a - (k * (k + 1) / 2) * b * d
{
    (k + 1) * a - (k * (k + 1) / 2) * b * d
}

function max3(x: int, y: int, z: int): int
    ensures max3(x, y, z) >= x && max3(x, y, z) >= y && max3(x, y, z) >= z
    ensures max3(x, y, z) == x || max3(x, y, z) == y || max3(x, y, z) == z
{
    if x >= y && x >= z then x
    else if y >= z then y
    else z
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, int, int)>) returns (results: seq<int>)
    requires ValidTestCases(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
{
    results := [];

    for i := 0 to |testCases|
        invariant 0 <= i <= |testCases|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            var (a, b, c, d) := testCases[j];
            (a - b * c > 0 ==> results[j] == -1) &&
            (a - b * c <= 0 && d >= c ==> results[j] == a) &&
            (a - b * c <= 0 && d < c ==> results[j] >= 0) &&
            results[j] >= -1
    {
        var (a, b, c, d) := testCases[i];
        var result: int;

        if a - b * c > 0 {
            result := -1;
        } else if d >= c {
            result := a;
        } else {
            var dn := 0;
            var up := 1000001;

            while up - dn > 1 
                invariant 0 <= dn < up <= 1000001
                invariant a >= 0 && b >= 0 && c >= 0 && d >= 0
                invariant forall k :: 0 <= k < dn ==> getSm(k, a, b, c, d) <= getSm(k + 1, a, b, c, d)
                invariant forall k :: up <= k && k < 1000001 ==> getSm(k, a, b, c, d) >= getSm(k + 1, a, b, c, d)
                decreases up - dn
            {
                var md := (up + dn) / 2;
                var sm1 := getSm(md, a, b, c, d);
                var sm2 := getSm(md + 1, a, b, c, d);

                if sm1 < sm2 {
                    dn := md;
                } else {
                    up := md;
                }
            }

            var smDn := getSm(dn, a, b, c, d);
            var smUp := getSm(up, a, b, c, d);
            result := max3(a, smDn, smUp);
        }

        results := results + [result];
    }
}
// </vc-code>
