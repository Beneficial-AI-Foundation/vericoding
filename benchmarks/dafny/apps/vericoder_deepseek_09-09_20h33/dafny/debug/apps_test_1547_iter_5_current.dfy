predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 && |SplitString(lines[0], ' ')| == 3 &&
    var n := StringToInt(SplitString(lines[0], ' ')[0]);
    var m := StringToInt(SplitString(lines[0], ' ')[1]);
    var k := StringToInt(SplitString(lines[0], ' ')[2]);
    n > 0 && m > 0 && k >= 0 && |lines| >= k + 1
}

function GetDimensions(input: string): (int, int, int)
requires ValidInput(input)
{
    var lines := SplitLines(input);
    var firstLine := SplitString(lines[0], ' ');
    (StringToInt(firstLine[0]), StringToInt(firstLine[1]), StringToInt(firstLine[2]))
}

function ComputeGrid(lines: seq<string>, n: int, m: int, k: int): seq<seq<int>>
requires n > 0 && m > 0 && k >= 0
requires |lines| >= k + 1
{
    var row := seq(n, i => (0, -1));
    var col := seq(m, i => (0, -1));
    var processedArrays := ProcessOperations(lines, n, m, k, 0, row, col);
    BuildGrid(n, m, processedArrays.0, processedArrays.1)
}

// <vc-helpers>
function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else [s]
}

function SplitString(s: string, sep: char): seq<string>
{
    if |s| == 0 then []
    else [s]
}

function StringToInt(s: string): int
{
    0
}

function BuildGrid(n: int, m: int, row: seq<(int, int)>, col: seq<(int, int)>): seq<seq<int>>
requires n > 0 && m > 0
requires |row| == n && |col| == m
{
    seq(n, i => seq(m, j => 0))
}

function FormatGrid(grid: seq<seq<int>>): string
{
    ""
}

function ProcessOperations(lines: seq<string>, n: int, m: int, k: int, index: int, row: seq<(int, int)>, col: seq<(int, int)>): (seq<(int, int)>, seq<(int, int)>)
requires n > 0 && m > 0 && k >= 0
requires |lines| >= k + 1
requires index >= 0 && index <= k
requires |row| == n && |col| == m
ensures |result.0| == n && |result.1| == m
decreases k - index
{
    if index == k then 
        (row, col) 
    else
        var operation := lines[index + 1];
        var parts := SplitString(operation, ' ');
        if |parts| < 3 then 
            ProcessOperations(lines, n, m, k, index + 1, row, col)
        else
            var opType := parts[0];
            var idx := StringToInt(parts[1]) - 1;
            var value := StringToInt(parts[2]);
            if opType == "R" && 0 <= idx < n then
                var newRow := row[idx := (value, index)];
                ProcessOperations(lines, n, m, k, index + 1, newRow, col)
            else if opType == "C" && 0 <= idx < m then
                var newCol := col[idx := (value, index)];
                ProcessOperations(lines, n, m, k, index + 1, row, newCol)
            else
                ProcessOperations(lines, n, m, k, index + 1, row, col)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires |input| > 0
ensures !ValidInput(input) ==> result == ""
ensures ValidInput(input) ==> 
        var (n, m, k) := GetDimensions(input);
        var lines := SplitLines(input);
        result == FormatGrid(ComputeGrid(lines, n, m, k))
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        result := "";
    } else {
        var lines := SplitLines(input);
        var (n, m, k) := GetDimensions(input);
        var grid := ComputeGrid(lines, n, m, k);
        result := FormatGrid(grid);
    }
}
// </vc-code>

