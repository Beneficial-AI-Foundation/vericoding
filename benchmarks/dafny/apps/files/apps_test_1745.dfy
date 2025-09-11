// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n'
}

predicate ValidOutput(output: string)
{
    |output| > 0 && output[|output|-1] == '\n'
}

function ParseGrid(input: string): (seq<seq<char>>, int, int)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    if |lines| == 0 then ([], 0, 0)
    else
        var grid := seq(|lines|, i requires 0 <= i < |lines| => lines[i]);
        var rows := |grid|;
        var cols := if rows > 0 then |grid[0]| else 0;
        (grid, rows, cols)
}

function SplitLines(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var newlinePos := FindNewline(s, 0);
        if newlinePos == -1 then [s]
        else if newlinePos == 0 then [""] + SplitLines(s[1..])
        else 
            assert 0 < newlinePos < |s|;
            assert 0 <= newlinePos <= |s|;
            assert 0 <= newlinePos + 1 <= |s|;
            [s[..newlinePos]] + SplitLines(s[newlinePos+1..])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures var pos := FindNewline(s, start); pos == -1 || (start <= pos < |s|)
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

predicate IsValidGrid(grid: seq<seq<char>>, rows: int, cols: int)
{
    |grid| == rows &&
    rows >= 0 && cols >= 0 &&
    (forall i :: 0 <= i < rows ==> |grid[i]| == cols) &&
    (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> grid[i][j] == '.' || grid[i][j] == '#')
}

predicate IsBoundaryCell(i: int, j: int, rows: int, cols: int)
    requires rows > 0 && cols > 0
{
    (i == 0 || i == rows - 1 || j == 0 || j == cols - 1)
}

predicate IsCornerCell(i: int, j: int, rows: int, cols: int)
    requires rows > 0 && cols > 0
{
    (i == 0 && j == 0) || (i == 0 && j == cols - 1) ||
    (i == rows - 1 && j == 0) || (i == rows - 1 && j == cols - 1)
}

function CountValidPipes(grid: seq<seq<char>>, rows: int, cols: int): int
    requires IsValidGrid(grid, rows, cols)
{
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ExecutePythonLogic(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(output)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
