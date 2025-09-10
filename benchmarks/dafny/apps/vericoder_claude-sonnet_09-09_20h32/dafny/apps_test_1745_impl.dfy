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
function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then IntToStringPos(n)
    else "-" + IntToStringPos(-n)
}

function IntToStringPos(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then [DigitToChar(n)]
    else IntToStringPos(n / 10) + [DigitToChar(n % 10)]
}

function DigitToChar(d: int): char
    requires 0 <= d <= 9
{
    match d
        case 0 => '0'
        case 1 => '1'
        case 2 => '2'
        case 3 => '3'
        case 4 => '4'
        case 5 => '5'
        case 6 => '6'
        case 7 => '7'
        case 8 => '8'
        case 9 => '9'
}

lemma IntToStringIsValid(n: int)
    ensures var s := IntToString(n); |s| > 0
{
    if n == 0 {
    } else if n > 0 {
        IntToStringPosIsValid(n);
    } else {
        IntToStringPosIsValid(-n);
    }
}

lemma IntToStringPosIsValid(n: int)
    requires n > 0
    ensures var s := IntToStringPos(n); |s| > 0
    decreases n
{
    if n < 10 {
    } else {
        IntToStringPosIsValid(n / 10);
    }
}

function NormalizeGrid(grid: seq<seq<char>>, rows: int, cols: int): seq<seq<char>>
{
    if rows == 0 || cols == 0 then []
    else
        seq(rows, i requires 0 <= i < rows => 
            if i < |grid| then NormalizeLine(grid[i], cols)
            else seq(cols, j => '.'))
}

function NormalizeLine(line: seq<char>, cols: int): seq<char>
{
    seq(cols, j => if j < |line| && (line[j] == '.' || line[j] == '#') then line[j] else '.')
}

lemma NormalizeGridIsValid(grid: seq<seq<char>>, rows: int, cols: int)
    requires rows >= 0 && cols >= 0
    ensures IsValidGrid(NormalizeGrid(grid, rows, cols), rows, cols)
{
    var normalized := NormalizeGrid(grid, rows, cols);
    if rows == 0 || cols == 0 {
    } else {
        forall i | 0 <= i < rows
            ensures |normalized[i]| == cols
            ensures forall j :: 0 <= j < cols ==> normalized[i][j] == '.' || normalized[i][j] == '#'
        {
            var line := normalized[i];
            forall j | 0 <= j < cols
                ensures line[j] == '.' || line[j] == '#'
            {
            }
        }
    }
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
    var normalizedGrid := NormalizeGrid(grid, rows, cols);
    NormalizeGridIsValid(grid, rows, cols);
    var count := CountValidPipes(normalizedGrid, rows, cols);
    IntToStringIsValid(count);
    var result := IntToString(count);
    output := result + "\n";
}
// </vc-code>

