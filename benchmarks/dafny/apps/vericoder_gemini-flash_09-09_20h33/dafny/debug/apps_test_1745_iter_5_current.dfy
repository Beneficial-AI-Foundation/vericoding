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
    0  // Simplified implementation
}

// <vc-helpers>
predicate IsWellFormedGrid(grid: seq<seq<char>>, rows: int, cols: int)
{
    |grid| == rows &&
    rows >= 0 && cols >= 0 &&
    (forall i :: 0 <= i < rows ==> |grid[i]| == cols)
}

function GridToString(grid: seq<seq<char>>): string
    requires IsWellFormedGrid(grid, |grid|, if |grid| > 0 then |grid[0]| else 0)
    ensures |GridToString(grid)| > 0 ==> GridToString(grid)[|GridToString(grid)|-1] == '\n'
{
    var rows := |grid|;
    if rows == 0 then "\n"
    else
        var s := "";
        var i := 0;
        while i < rows
            invariant 0 <= i <= rows
            invariant s == SeqToString(grid[..i])
            invariant IsWellFormedGrid(grid, rows, if rows > 0 then |grid[0]| else 0)
        {
            s := s + SeqToChars(grid[i]) + "\n";
            i := i + 1;
        }
        s
}
function SeqToString(seq_of_seq: seq<seq<char>>): string {
  if |seq_of_seq| == 0 then ""
  else (SeqToChars(seq_of_seq[0]) + "\n" + SeqToString(seq_of_seq[1..]))
}

function SeqToChars(s: seq<char>): string {
    if |s| == 0 then ""
    else
        var res := "";
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant res == (if i == 0 then "" else s[..i] + "")
        {
            res := res + (s[i] + "");
            i := i + 1;
        }
        res
}
// </vc-helpers>

// <vc-spec>
method ExecutePythonLogic(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(output)
// </vc-spec>
// <vc-code>
{
    var (grid, rows, cols) := ParseGrid(input);

    var temp_grid := grid; // Create a mutable copy of the grid sequence

    // Apply the specified logic to modify temp_grid based on the rules.
    // The details of the logic come from problem description 
    // about modifying boundary cells and interior cells.
    for i := 0 to rows - 1
        invariant 0 <= i <= rows
        invariant IsWellFormedGrid(temp_grid, rows, cols)
    {
        for j := 0 to cols - 1
            invariant 0 <= j <= cols
            invariant IsWellFormedGrid(temp_grid, rows, cols)
        {
            if (rows > 0 && cols > 0 && (i == 0 || i == rows - 1 || j == 0 || j == cols - 1)) { // Boundary cell
                if (rows > 0 && cols > 0 && ((i == 0 && j == 0) || (i == 0 && j == cols - 1) ||
                   (i == rows - 1 && j == 0) || (i == rows - 1 && j == cols - 1))) { // Corner cell
                    // Corners remain as they are
                } else { // Edge cell (non-corner boundary)
                    if temp_grid[i][j] == '.' {
                        temp_grid := temp_grid[i := temp_grid[i][j := '#']]; // Change to '#'
                    }
                }
            } else { // Interior cell
                if rows > 0 && cols > 0 && temp_grid[i][j] == '#' {
                    temp_grid := temp_grid[i := temp_grid[i][j := '.']]; // Change to '.'
                }
            }
        }
    }
    output := GridToString(temp_grid);
}
// </vc-code>

