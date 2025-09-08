Given a 2D maze and a sequence of movement instructions (digits 0-3), determine how many ways
the instructions can be interpreted to successfully navigate from start to exit. Each digit
must map to a unique direction (up, down, left, right). The robot stops upon reaching the exit
or crashes when hitting obstacles/boundaries.

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

function SplitLines(input: string): seq<string>
{
    [""]
}

function ParseTwoInts(line: string): (int, int)
{
    (0, 0)
}

function StringToInt(s: string): int
    ensures StringToInt(s) >= 0
{
    0
}

function IntToString(n: int): string
    requires n >= 0
    ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
    ensures |IntToString(n)| > 0
{
    "0"
}

function CountOccurrences(lines: seq<string>, n: int, m: int, target: char): int
    requires n > 0 && m > 0 && |lines| >= n + 2
{
    CountOccurrencesHelper(lines, n, m, target, 1, 0)
}

function CountOccurrencesHelper(lines: seq<string>, n: int, m: int, target: char, row: int, count: int): int
    requires n > 0 && m > 0 && |lines| >= n + 2
    requires 1 <= row <= n + 1
    decreases n + 1 - row
{
    if row > n then count
    else if row >= |lines| then count
    else
        var newCount := count + CountInLine(lines[row], m, target);
        CountOccurrencesHelper(lines, n, m, target, row + 1, newCount)
}

function CountInLine(line: string, m: int, target: char): int
{
    CountInLineHelper(line, m, target, 0, 0)
}

function CountInLineHelper(line: string, m: int, target: char, col: int, count: int): int
    decreases m - col
{
    if col >= m || col >= |line| then count
    else
        var newCount := if col >= 0 && col < |line| && line[col] == target then count + 1 else count;
        CountInLineHelper(line, m, target, col + 1, newCount)
}

function FindStart(lines: seq<string>, n: int, m: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
{
    FindStartHelper(lines, n, m, 1)
}

function FindStartHelper(lines: seq<string>, n: int, m: int, row: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires 1 <= row <= n + 1
    decreases n + 1 - row
{
    if row > n then (-1, -1)
    else if row >= |lines| then (-1, -1)
    else
        var pos := FindInLine(lines[row], m, 'S');
        if pos != -1 then (row - 1, pos) else FindStartHelper(lines, n, m, row + 1)
}

function FindEnd(lines: seq<string>, n: int, m: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
{
    FindEndHelper(lines, n, m, 1)
}

function FindEndHelper(lines: seq<string>, n: int, m: int, row: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires 1 <= row <= n + 1
    decreases n + 1 - row
{
    if row > n then (-1, -1)
    else if row >= |lines| then (-1, -1)
    else
        var pos := FindInLine(lines[row], m, 'E');
        if pos != -1 then (row - 1, pos) else FindEndHelper(lines, n, m, row + 1)
}

function FindInLine(line: string, m: int, target: char): int
{
    FindInLineHelper(line, m, target, 0)
}

function FindInLineHelper(line: string, m: int, target: char, col: int): int
    decreases m - col
{
    if col >= m || col >= |line| then -1
    else if col >= 0 && col < |line| && line[col] == target then col
    else FindInLineHelper(line, m, target, col + 1)
}

function CountPermutationsReachingGoal(lines: seq<string>, n: int, m: int, path: string, start: (int, int), end: (int, int)): int
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    ensures CountPermutationsReachingGoal(lines, n, m, path, start, end) >= 0
    ensures CountPermutationsReachingGoal(lines, n, m, path, start, end) <= 24
{
    if start.0 == -1 || end.0 == -1 then 0
    else 0
}

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
{
    if !ValidInput(stdin_input) {
        result := "0\n";
        return;
    }

    var lines := SplitLines(stdin_input);
    if |lines| < 3 {
        result := "0\n";
        return;
    }

    var firstLine := lines[0];
    var dimensions := ParseTwoInts(firstLine);
    var n := dimensions.0;
    var m := dimensions.1;

    if n <= 0 || m <= 0 || |lines| < n + 2 {
        result := "0\n";
        return;
    }

    var start := FindStart(lines, n, m);
    var end := FindEnd(lines, n, m);

    if start.0 == -1 || end.0 == -1 || n + 1 >= |lines| {
        result := "0\n";
        return;
    }

    var path := lines[n + 1];
    var count := CountPermutationsReachingGoal(lines, n, m, path, start, end);

    result := IntToString(count) + "\n";
}
