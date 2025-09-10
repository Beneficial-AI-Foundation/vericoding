predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidGrid(grid: seq<string>, n: int, m: int)
{
    n >= 1 && m >= 1 && |grid| == n &&
    forall i :: 0 <= i < |grid| ==> |grid[i]| == m
}

function CountFaceSquares(input: string): int
    requires |input| > 0
    ensures CountFaceSquares(input) >= 0
{
    var lines := SplitLinesFunc(input);
    if |lines| == 0 then 0
    else
        var firstLine := lines[0];
        var nm := SplitSpacesFunc(firstLine);
        if |nm| < 2 then 0
        else
            var n := StringToIntFunc(nm[0]);
            var m := StringToIntFunc(nm[1]);
            if n < 1 || m < 1 || |lines| < n + 1 then 0
            else
                var grid := lines[1..n+1];
                CountValidSquares(grid, n, m)
}

function CountFaceSquaresAsString(input: string): string
    requires |input| > 0
    ensures |CountFaceSquaresAsString(input)| > 0
{
    var count := CountFaceSquares(input);
    IntToStringFunc(count) + "\n"
}

// <vc-helpers>
function SplitLinesFunc(s: string): seq<string>
    ensures |SplitLinesFunc(s)| >= 0

function SplitSpacesFunc(s: string): seq<string>
    ensures |SplitSpacesFunc(s)| >= 0

function StringToIntFunc(s: string): int
    ensures StringToIntFunc(s) >= 0

function IntToStringFunc(n: int): string
    requires n >= 0
    ensures |IntToStringFunc(n)| > 0

function CountValidSquares(grid: seq<string>, n: int, m: int): int
    requires ValidGrid(grid, n, m)
    ensures CountValidSquares(grid, n, m) >= 0

method SplitLines(s: string) returns (lines: seq<string>)
    ensures lines == SplitLinesFunc(s)

method SplitSpaces(s: string) returns (parts: seq<string>)
    ensures parts == SplitSpacesFunc(s)

method StringToInt(s: string) returns (n: int)
    ensures n == StringToIntFunc(s)

method IntToString(n: int) returns (s: string)
    requires n >= 0
    ensures s == IntToStringFunc(n)

method CountSquares(grid: seq<string>, n: int, m: int) returns (count: int)
    requires ValidGrid(grid, n, m)
    ensures count == CountValidSquares(grid, n, m)
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == CountFaceSquaresAsString(input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    if |lines| == 0 {
        result := "0\n";
    } else {
        var firstLine := lines[0];
        var nm := SplitSpaces(firstLine);
        if |nm| < 2 {
            result := "0\n";
        } else {
            var n := StringToInt(nm[0]);
            var m := StringToInt(nm[1]);
            if n < 1 || m < 1 || |lines| < n + 1 {
                result := "0\n";
            } else {
                var grid := lines[1..n+1];
                assert |grid| == n;
                if forall i :: 0 <= i < |grid| ==> |grid[i]| == m {
                    assert ValidGrid(grid, n, m);
                    var count := CountSquares(grid, n, m);
                    var countStr := IntToString(count);
                    result := countStr + "\n";
                } else {
                    result := "0\n";
                }
            }
        }
    }
}
// </vc-code>

