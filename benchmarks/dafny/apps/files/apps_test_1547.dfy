Given an n×m grid initially filled with color 0, perform k painting operations and output the final grid.
Operations can paint entire rows or columns with specified colors.
When a cell is painted multiple times, it takes the color of the most recent operation affecting it.

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

function ProcessOperations(lines: seq<string>, n: int, m: int, k: int, opIndex: int, row: seq<(int, int)>, col: seq<(int, int)>): (seq<(int, int)>, seq<(int, int)>)
requires n > 0 && m > 0 && k >= 0 && opIndex >= 0
requires |lines| >= k + 1
requires |row| == n && |col| == m
ensures |ProcessOperations(lines, n, m, k, opIndex, row, col).0| == n
ensures |ProcessOperations(lines, n, m, k, opIndex, row, col).1| == m
decreases k - opIndex
{
    if opIndex >= k || 1 + opIndex >= |lines| then
        (row, col)
    else
        var opLine := SplitString(lines[1 + opIndex], ' ');
        if |opLine| == 3 then
            var t := StringToInt(opLine[0]);
            var num := StringToInt(opLine[1]) - 1;
            var color := StringToInt(opLine[2]);
            if t == 1 && 0 <= num < n then
                ProcessOperations(lines, n, m, k, opIndex + 1, row[num := (color, opIndex)], col)
            else if t == 2 && 0 <= num < m then
                ProcessOperations(lines, n, m, k, opIndex + 1, row, col[num := (color, opIndex)])
            else
                ProcessOperations(lines, n, m, k, opIndex + 1, row, col)
        else
            ProcessOperations(lines, n, m, k, opIndex + 1, row, col)
}

function BuildGrid(n: int, m: int, row: seq<(int, int)>, col: seq<(int, int)>): seq<seq<int>>
requires n > 0 && m > 0
requires |row| == n && |col| == m
ensures |BuildGrid(n, m, row, col)| == n
ensures forall i :: 0 <= i < n ==> |BuildGrid(n, m, row, col)[i]| == m
{
    seq(n, r requires 0 <= r < n => seq(m, c requires 0 <= c < m => if col[c].1 > row[r].1 then col[c].0 else row[r].0))
}

function FormatGrid(grid: seq<seq<int>>): string
{
    if |grid| == 0 then
        ""
    else
        FormatGridHelper(grid, 0, "")
}

function FormatGridHelper(grid: seq<seq<int>>, rowIndex: int, acc: string): string
requires 0 <= rowIndex <= |grid|
decreases |grid| - rowIndex
{
    if rowIndex >= |grid| then
        acc
    else
        var rowStr := FormatRow(grid[rowIndex]);
        var newAcc := if rowIndex == 0 then rowStr else acc + "\n" + rowStr;
        FormatGridHelper(grid, rowIndex + 1, newAcc)
}

function FormatRow(row: seq<int>): string
{
    if |row| == 0 then
        ""
    else
        FormatRowHelper(row, 0, "")
}

function FormatRowHelper(row: seq<int>, colIndex: int, acc: string): string
requires 0 <= colIndex <= |row|
decreases |row| - colIndex
{
    if colIndex >= |row| then
        acc
    else
        var numStr := IntToString(row[colIndex]);
        var newAcc := if colIndex == 0 then numStr else acc + " " + numStr;
        FormatRowHelper(row, colIndex + 1, newAcc)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n, "")
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
requires n >= 0
decreases n
{
    if n == 0 then
        if acc == "" then "0" else acc
    else
        IntToStringHelper(n / 10, [('0' as int + n % 10) as char] + acc)
}

function SplitLines(s: string): seq<string>
{
    SplitString(s, '\n')
}

function SplitString(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then
        [""]
    else
        SplitStringHelper(s, delimiter, 0, [])
}

function SplitStringHelper(s: string, delimiter: char, start: int, acc: seq<string>): seq<string>
requires 0 <= start <= |s|
decreases |s| - start
{
    if start >= |s| then
        acc
    else
        var end := FindDelimiter(s, delimiter, start);
        var part := s[start..end];
        var newAcc := acc + [part];
        if end >= |s| then
            newAcc
        else
            SplitStringHelper(s, delimiter, end + 1, newAcc)
}

function FindDelimiter(s: string, delimiter: char, start: int): int
requires 0 <= start <= |s|
ensures start <= FindDelimiter(s, delimiter, start) <= |s|
decreases |s| - start
{
    if start >= |s| then
        |s|
    else if s[start] == delimiter then
        start
    else
        FindDelimiter(s, delimiter, start + 1)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then
        -StringToIntHelper(s[1..], 0)
    else
        StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
decreases |s|
{
    if |s| == 0 then
        acc
    else if '0' <= s[0] <= '9' then
        StringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
    else
        acc
}

method solve(input: string) returns (result: string)
requires |input| > 0
ensures !ValidInput(input) ==> result == ""
ensures ValidInput(input) ==> 
        var (n, m, k) := GetDimensions(input);
        var lines := SplitLines(input);
        result == FormatGrid(ComputeGrid(lines, n, m, k))
{
    var lines := SplitLines(input);
    if |lines| == 0 {
        return "";
    }

    var firstLine := SplitString(lines[0], ' ');
    if |firstLine| != 3 {
        return "";
    }

    var n := StringToInt(firstLine[0]);
    var m := StringToInt(firstLine[1]);
    var k := StringToInt(firstLine[2]);

    if n <= 0 || m <= 0 || k < 0 {
        return "";
    }

    if |lines| < k + 1 {
        return "";
    }

    result := FormatGrid(ComputeGrid(lines, n, m, k));
}
