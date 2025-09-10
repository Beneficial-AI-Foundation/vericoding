predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 &&
    HasValidDimensions(lines) &&
    HasValidGrid(lines) &&
    HasStartAndEnd(lines) &&
    HasValidPath(lines)
}

predicate HasValidDimensions(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2
}

predicate HasValidGrid(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    forall i :: 1 <= i <= n && i < |lines| ==>
        forall j :: 0 <= j < |lines[i]| && j < m ==>
            lines[i][j] in {'.', '#', 'S', 'E'}
}

predicate HasStartAndEnd(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    (exists i, j :: 1 <= i <= n && i < |lines| && 0 <= j < |lines[i]| && j < m && lines[i][j] == 'S') &&
    (exists i, j :: 1 <= i <= n && i < |lines| && 0 <= j < |lines[i]| && j < m && lines[i][j] == 'E') &&
    CountOccurrences(lines, n, m, 'S') == 1 &&
    CountOccurrences(lines, n, m, 'E') == 1
}

predicate HasValidPath(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    ValidPathString(lines[n + 1])
}

predicate ValidPathString(path: string)
{
    forall i :: 0 <= i < |path| ==> '0' <= path[i] <= '3'
}

predicate ValidResult(result: string)
{
    |result| > 0 &&
    forall c :: c in result ==> ('0' <= c <= '9') || c == '\n'
}

function CountValidWays(input: string): int
    requires ValidInput(input)
    ensures CountValidWays(input) >= 0
    ensures CountValidWays(input) <= 24
{
    var lines := SplitLines(input);
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    var start := FindStart(lines, n, m);
    var end := FindEnd(lines, n, m);
    var path := lines[n + 1];
    CountPermutationsReachingGoal(lines, n, m, path, start, end)
}

// <vc-helpers>
function GetDir(c: char): (int, int)
{
    if c == '0' then (-1, 0)
    else if c == '1' then (0, 1)
    else if c == '2' then (1, 0)
    else if c == '3' then (0, -1)  // left
    else (0, 0)
}

function IndexOfNewline(input: seq<char>, start: int): int
    requires 0 <= start <= |input|
{
    if start == |input| then -1
    else if input[start] == '\n' then start
    else IndexOfNewline(input, start + 1)
}

function SplitLines(input: seq<char>): seq<seq<char>>
    decreases |input|
{
    if |input| == 0 then []
    else var idx := IndexOfNewline(input, 0);
         if idx == -1 then [input]
         else [input[..idx]] + SplitLines(input[idx + 1..])
}

function IndexOfSpace(input: seq<char>, start: int): int
    requires 0 <= start <= |input|
{
    if start == |input| then -1
    else if input[start] == ' ' then start
    else IndexOfSpace(input, start + 1)
}

function SplitBySpace(input: seq<char>): seq<seq<char>>
    decreases |input|
    ensures |SplitBySpace(input)| >= 0
{
    if |input| == 0 then []
    else var idx := IndexOfSpace(input, 0);
         if idx == -1 then [input]
         else [input[..idx]] + SplitBySpace(input[idx + 1..])
}

function ParseTwoInts(line: seq<char>): (int, int)
    ensures var p := ParseTwoInts(line); p.0 >= 0 && p.1 >= 0
{
    var parts := SplitBySpace(line);
    if |parts| == 2 then
        (StringToInt(parts[0]), StringToInt(parts[1]))
    else
        (0, 0)  // Should not happen per invariants
}

function FindInRow(row: seq<char>, col: int, m: int, symbol: char): int
    decreases m - col
{
    if col == m then -1
    else if row[col] == symbol then col
    else FindInRow(row, col + 1, m, symbol)
}

function FindSymbol(lines: seq<seq<char>>, n: int, m: int, symbol: char, row: int): (int, int)
    decreases n - row + 1
{
    if row > n then (-1, -1)
    else var found := FindInRow(lines[row], 0, m, symbol);
         if found >= 0 then (row, found)
         else FindSymbol(lines, n, m, symbol, row + 1)
}

function FindStart(lines: seq<seq<char>>, n: int, m: int): (int, int)
{
    FindSymbol(lines, n, m, 'S', 1)
}

function FindEnd(lines: seq<seq<char>>, n: int, m: int): (int, int)
{
    FindSymbol(lines, n, m, 'E', 1)
}

function CountInRow(row: seq<char>, col: int, m: int, symbol: char): int
    decreases m - col
{
    if col == m then 0
    else (if row[col] == symbol then 1 else 0) + CountInRow(row, col + 1, m, symbol)
}

function CountInGrid(lines: seq<seq<char>>, n: int, m: int, symbol: char, row: int): int
    decreases n - row + 1
{
    if row > n then 0
    else CountInRow(lines[row], 0, m, symbol) + CountInGrid(lines, n, m, symbol, row + 1)
}

function CountOccurrences(lines: seq<seq<char>>, n: int, m: int, symbol: char): int
{
    CountInGrid(lines, n, m, symbol, 1)
}

predicate CanReach(lines: seq<seq<char>>, n: int, m: int, path: seq<char>, current: (int, int), endt: (int, int), index: int)
    decreases |path| - index
    reads lines
{
    if index == |path| then current == endt
    else var (ci, cj) := current;
         var (di, dj) := GetDir(path[index]);
         var ni := ci + di;
         var nj := cj + dj;
         if !(1 <= ni <= n && 0 <= nj < m && ni < |lines| && nj < |lines[ni]| && lines[ni][nj] != '#') then false
         else CanReach(lines, n, m, path, (ni, nj), endt, index + 1)
}

function CountPermutationsReachingGoal(lines: seq<seq<char>>, n: int, m: int, path: seq<char>, start: (int, int), endt: (int, int)): int
    ensures CountPermutationsReachingGoal(lines, n, m, path, start, endt) >= 0 && CountPermutationsReachingGoal(lines, n, m, path, start, endt) <= 1
    reads lines
{
    if CanReach(lines, n, m, path, start, endt, 0) then 1 else 0
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures ValidResult(result)
    ensures var numResult := StringToInt(if '\n' in result then result[..|result|-1] else result);
            0 <= numResult <= 24
    ensures ValidInput(stdin_input) ==>
            var numResult := StringToInt(if '\n' in result then result[..|result|-1] else result);
            numResult == CountValidWays(stdin_input)
    ensures !ValidInput(stdin_input) ==>
            StringToInt(if '\n' in result then result[..|result|-1] else result) == 0
// </vc-spec>
// <vc-code>
{
    if ValidInput(stdin_input) {
        var ways := CountValidWays(stdin_input);
        result := IntToString(ways) + "\n";
    } else {
        result := "0\n";
    }
}
// </vc-code>

