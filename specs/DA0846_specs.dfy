// <vc-preamble>
predicate ValidInput(a: int, b: int, c: int, n: int)
{
    a >= 1 && b >= 1 && c >= 1 && n >= 1 &&
    a <= 100000000 && b <= 100000000 && c <= 100000000 && n <= 100000000
}

predicate ValidTestCases(testCases: seq<(int, int, int, int)>)
{
    forall i :: 0 <= i < |testCases| ==> ValidInput(testCases[i].0, testCases[i].1, testCases[i].2, testCases[i].3)
}

function CanDistributeEqually(a: int, b: int, c: int, n: int): bool
    requires ValidInput(a, b, c, n)
{
    var maxVal := max3(a, b, c);
    var totalSum := a + b + c + n;
    totalSum % 3 == 0 && maxVal <= totalSum / 3
}

function ProcessTestCaseResult(a: int, b: int, c: int, n: int): string
    requires ValidInput(a, b, c, n)
{
    if CanDistributeEqually(a, b, c, n) then "YES" else "NO"
}

predicate ValidResults(testCases: seq<(int, int, int, int)>, results: seq<string>)
    requires ValidTestCases(testCases)
{
    |results| == |testCases| &&
    forall i :: 0 <= i < |testCases| ==> 
        results[i] == ProcessTestCaseResult(testCases[i].0, testCases[i].1, testCases[i].2, testCases[i].3) &&
        (results[i] == "YES" || results[i] == "NO")
}
// </vc-preamble>

// <vc-helpers>
function max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, int, int)>) returns (results: seq<string>)
    requires ValidTestCases(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < |testCases|
        invariant 0 <= i <= |testCases|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            results[j] == ProcessTestCaseResult(testCases[j].0, testCases[j].1, testCases[j].2, testCases[j].3)
        invariant forall j :: 0 <= j < i ==> 
            results[j] == "YES" || results[j] == "NO"
    {
        var (a, b, c, n) := testCases[i];
        var result := ProcessTestCaseResult(a, b, c, n);
        results := results + [result];
        i := i + 1;
    }
}
// </vc-code>
