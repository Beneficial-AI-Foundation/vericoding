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
function SplitLinesHelper(s: string, current: string): seq<string>
decreases |s|
{
    if s == "" then [current]
    else 
        var c := s[0];
        if c == '\n' then
            [current] + SplitLinesHelper(s[1..], "")
        else
            SplitLinesHelper(s[1..], current + [c])
}

function SplitLines(s: string): seq<string>
{
    if s == "" then []
    else SplitLinesHelper(s, "")
}

function SplitStringHelper(s: string, sep: char, current: string, result: seq<string>): seq<string>
decreases |s|
{
    if s == "" then 
        if current != "" then result + [current] else result
    else
        var c := s[0];
        if c == sep then
            if current != "" then 
                SplitStringHelper(s[1..], sep, "", result + [current])
            else
                SplitStringHelper(s[1..], sep, "", result)
        else
            SplitStringHelper(s[1..], sep, current + [c], result)
}

function SplitString(s: string, sep: char): seq<string>
{
    SplitStringHelper(s, sep, "", [])
}

function StringToInt(s: string): int
decreases |s|
{
    if |s| == 0 then 0
    else StringToInt(s[0..|s|-1]) * 10 + (ord(s[|s|-1]) - ord('0'))
}

function IntToString(i: int): string
{
    if i == 0 then "0"
    else if i > 0 then IntToStringHelper(i, [])
    else "-" + IntToStringHelper(-i, [])
}

function IntToStringHelper(i: int, acc: seq<char>): string
decreases i
{
    if i == 0 then acc
    else
        var digit := i % 10;
        var charDigit := ['0','1','2','3','4','5','6','7','8','9'][digit];
        IntToStringHelper(i / 10, [charDigit] + acc)
}

function FormatRow(row: seq<int>): string
decreases |row|
{
    if |row| == 0 then ""
    else if |row| == 1 then IntToString(row[0])
    else IntToString(row[0]) + " " + FormatRow(row[1..])
}

function FormatGrid(grid: seq<seq<int>>): string
decreases |grid|
{
    if |grid| == 0 then ""
    else if |grid| == 1 then FormatRow(grid[0])
    else FormatRow(grid[0]) + "\n" + FormatGrid(grid[1..])
}

function ProcessOperations(lines: seq<string>, n: int, m: int, k: int, opIndex: int, 
                          row: seq<(int, int)>, col: seq<(int, int)>): (seq<(int, int)>, seq<(int, int)>)
requires |lines| >= k + 1
requires |row| == n
requires |col| == m
requires 0 <= opIndex <= k
decreases k - opIndex
{
    if opIndex == k then (row, col)
    else
        var opLine := lines[1 + opIndex];
        var parts := SplitString(opLine, ' ');
        if |parts| < 3 then 
            ProcessOperations(lines, n, m, k, opIndex+1, row, col)
        else
            var opType := parts[0];
            var index := StringToInt(parts[1]);
            var x := StringToInt(parts[2]);
            if opType == "r" && 1 <= index <= n then
                var rowIndex := index - 1;
                var newRow := row[rowIndex := (x, opIndex)];
                ProcessOperations(lines, n, m, k, opIndex+1, newRow, col)
            else if opType == "c" && 1 <= index <= m then
                var colIndex := index - 1;
                var newCol := col[colIndex := (x, opIndex)];
                ProcessOperations(lines, n, m, k, opIndex+1, row, newCol)
            else
                ProcessOperations(lines, n, m, k, opIndex+1, row, col)
}

function BuildGrid(n: int, m: int, row: seq<(int, int)>, col: seq<(int, int)>): seq<seq<int>>
requires n > 0 && m > 0
requires |row| == n
requires |col| == m
{
    seq(n, i => seq(m, j => if row[i].1 >= col[j].1 then row[i].0 else col[j].0))
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
        return "";
    } else {
        var (n, m, k) := GetDimensions(input);
        var lines := SplitLines(input);
        var grid := ComputeGrid(lines, n, m, k);
        return FormatGrid(grid);
    }
}
// </vc-code>

