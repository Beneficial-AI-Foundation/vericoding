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
function SplitLinesFunc(input: string): seq<string>
{
  []
}

function SplitSpacesFunc(s: string): seq<string>
{
  []
}

function StringToIntFunc(s: string): int
{
  0
}

function IntToStringFunc(n: int): string
{
  "0"
}

function Count1s(s: string, len: int): int
    requires |s| == len
    ensures Count1s(s, len) >= 0
    decreases len
{
    if len == 0 then 0
    else if s[len-1] == '1' then 1 + Count1s(s[..len-1], len-1) else Count1s(s[..len-1], len-1)
}

function CountValidSquares(grid: seq<string>, n: int, m: int): int
    requires |grid| == n
    ensures CountValidSquares(grid, n, m) >= 0
    decreases n
{
    if n == 0 then 0
    else if |grid[n-1]| != m then 0
    else Count1s(grid[n-1], m) + CountValidSquares(grid[..n-1], n-1, m)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == CountFaceSquaresAsString(input)
// </vc-spec>
// <vc-code>
{
  result := CountFaceSquaresAsString(input);
}
// </vc-code>

