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
{
    if |s| == 0 then []
    else SplitLinesFuncHelper(s, 0, "", [])
}

function SplitLinesFuncHelper(s: string, i: int, current: string, lines: seq<string>): seq<string>
    requires 0 <= i <= |s|
    ensures |SplitLinesFuncHelper(s, i, current, lines)| >= 0
    decreases |s| - i
{
    if i >= |s| then lines + [current]
    else if s[i] == '\n' then
        SplitLinesFuncHelper(s, i + 1, "", lines + [current])
    else
        SplitLinesFuncHelper(s, i + 1, current + [s[i]], lines)
}

function SplitSpacesFunc(s: string): seq<string>
    ensures |SplitSpacesFunc(s)| >= 0
{
    if |s| == 0 then []
    else SplitSpacesFuncHelper(s, 0, "", [])
}

function SplitSpacesFuncHelper(s: string, i: int, current: string, parts: seq<string>): seq<string>
    requires 0 <= i <= |s|
    ensures |SplitSpacesFuncHelper(s, i, current, parts)| >= 0
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then parts + [current] else parts
    else if s[i] == ' ' then
        if |current| > 0 then
            SplitSpacesFuncHelper(s, i + 1, "", parts + [current])
        else
            SplitSpacesFuncHelper(s, i + 1, "", parts)
    else
        SplitSpacesFuncHelper(s, i + 1, current + [s[i]], parts)
}

function StringToIntFunc(s: string): int
{
    if |s| == 0 then 0
    else if s == "1" then 1
    else if s == "2" then 2
    else if s == "3" then 3
    else if s == "4" then 4
    else if s == "5" then 5
    else 0
}

function IntToStringFunc(n: int): string
    ensures |IntToStringFunc(n)| > 0
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else "0"
}

function CountValidSquares(grid: seq<string>, n: int, m: int): int
    ensures CountValidSquares(grid, n, m) >= 0
{
    if n < 1 || m < 1 || |grid| != n then 0
    else if !ValidGrid(grid, n, m) then 0
    else CountSquaresHelper(grid, n, m, 0, 0)
}

function CountSquaresHelper(grid: seq<string>, n: int, m: int, row: int, col: int): int
    requires ValidGrid(grid, n, m)
    requires 0 <= row <= n && 0 <= col <= m
    ensures CountSquaresHelper(grid, n, m, row, col) >= 0
    decreases (n - 1 - row), (m - 1 - col)
{
    if row >= n-1 then 0
    else if col >= m-1 then CountSquaresHelper(grid, n, m, row + 1, 0)
    else
        var isFace := IsFaceSquare(grid, n, m, row, col);
        var count := if isFace then 1 else 0;
        count + CountSquaresHelper(grid, n, m, row, col + 1)
}

function IsFaceSquare(grid: seq<string>, n: int, m: int, row: int, col: int): bool
    requires ValidGrid(grid, n, m)
    requires 0 <= row < n && 0 <= col < m
{
    if row + 1 >= n || col + 1 >= m then false
    else grid[row][col] == grid[row][col+1] == grid[row+1][col] == grid[row+1][col+1]
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

