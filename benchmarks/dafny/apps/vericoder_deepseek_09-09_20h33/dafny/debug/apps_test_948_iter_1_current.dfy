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
predicate ValidSquare(grid: seq<string>, n: int, m: int, i: int, j: int)
{
    var c := grid[i][j];
    grid[i-1][j] == c && grid[i][j-1] == c && grid[i-1][j-1] == c &&
    grid[i+1][j] == c && grid[i][j+1] == c && grid[i+1][j+1] == c &&
    grid[i-1][j+1] == c && grid[i+1][j-1] == c
}

function CountValidSquares(grid: seq<string>, n: int, m: int): int
    requires ValidGrid(grid, n, m)
    ensures CountValidSquares(grid, n, m) >= 0
{
    if n < 3 || m < 3 then 0
    else CountValidSquaresHelper(grid, n, m, 1, 0)
}

function CountValidSquaresHelper(grid: seq<string>, n: int, m: int, i: int, count: int): int
    requires ValidGrid(grid, n, m)
    requires 1 <= i <= n - 1
    requires count >= 0
    ensures CountValidSquaresHelper(grid, n, m, i, count) >= count
{
    if i >= n - 1 then count
    else
        var newCount := CountValidSquaresRow(grid, n, m, i, 1, count);
        CountValidSquaresHelper(grid, n, m, i + 1, newCount)
}

function CountValidSquaresRow(grid: seq<string>, n: int, m: int, i: int, j: int, count: int): int
    requires ValidGrid(grid, n, m)
    requires 1 <= i < n - 1
    requires 1 <= j <= m - 1
    requires count >= 0
    ensures CountValidSquaresRow(grid, n, m, i, j, count) >= count
{
    if j >= m - 1 then count
    else
        var newCount := if ValidSquare(grid, n, m, i, j) then count + 1 else count;
        CountValidSquaresRow(grid, n, m, i, j + 1, newCount)
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
  var lines := SplitLinesFunc(input);
  var firstLine := lines[0];
  var nm := SplitSpacesFunc(firstLine);
  var n := StringToIntFunc(nm[0]);
  var m := StringToIntFunc(nm[1]);
  var grid := lines[1..n+1];
  var count := CountValidSquares(grid, n, m);
  result := IntToStringFunc(count) + "\n";
}
// </vc-code>

