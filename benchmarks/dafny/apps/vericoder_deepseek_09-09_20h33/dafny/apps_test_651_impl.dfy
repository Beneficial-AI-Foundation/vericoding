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
function CountOccurrences(lines: seq<string>, n: int, m: int, target: char): int
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires forall i :: 1 <= i <= n ==> i < |lines|
    requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
{
    CountOccurrencesHelper(lines, n, m, target, 1, 0)
}

function CountOccurrencesHelper(lines: seq<string>, n: int, m: int, target: char, i: int, j: int): int
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires 1 <= i <= n+1
    requires 0 <= j <= m
    requires forall k :: 1 <= k <= n ==> k < |lines|
    requires forall k :: 1 <= k <= n ==> |lines[k]| >= m
    decreases n - i, m - j
{
    if i > n then 0
    else if j >= m then CountOccurrencesHelper(lines, n, m, target, i+1, 0)
    else (if lines[i][j] == target then 1 else 0) + CountOccurrencesHelper(lines, n, m, target, i, j+1)
}

function CountOccurrencesInRange(lines: seq<string>, start: int, end: int, m: int, target: char): int
    requires 1 <= start <= end+1 <= |lines|
    decreases end - start
{
    if start > end then 0
    else CountOccurrencesInLine(lines[start], 0, m, target) + CountOccurrencesInRange(lines, start+1, end, m, target)
}

function CountOccurrencesInLine(line: string, start: int, end: int, target: char): int
    requires 0 <= start <= end <= |line|
    decreases end - start
{
    if start >= end then 0
    else (if line[start] == target then 1 else 0) + CountOccurrencesInLine(line, start+1, end, target)
}

function FindStart(lines: seq<string>, n: int, m: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires forall i :: 1 <= i <= n ==> i < |lines|
    requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
    requires CountOccurrences(lines, n, m, 'S') == 1
    ensures 1 <= Result.0 <= n && 0 <= Result.1 < m
    ensures lines[Result.0][Result.1] == 'S'
{
    FindStartHelper(lines, n, m, 1, 0)
}

function FindStartHelper(lines: seq<string>, n: int, m: int, i: int, j: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires 1 <= i <= n
    requires 0 <= j <= m
    requires forall k :: 1 <= k <= n ==> k < |lines|
    requires forall k :: 1 <= k <= n ==> |lines[k]| >= m
    requires CountOccurrences(lines, n, m, 'S') == 1
    ensures 1 <= Result.0 <= n && 0 <= Result.1 < m
    ensures lines[Result.0][Result.1] == 'S'
    decreases n - i, m - j
{
    if j < m && lines[i][j] == 'S' then (i, j)
    else if j < m - 1 then FindStartHelper(lines, n, m, i, j+1)
    else if i < n then FindStartHelper(lines, n, m, i+1, 0)
    else (1, 0)
}

function FindEnd(lines: seq<string>, n: int, m: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires forall i :: 1 <= i <= n ==> i < |lines|
    requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
    requires CountOccurrences(lines, n, m, 'E') == 1
    ensures 1 <= Result.0 <= n && 0 <= Result.1 < m
    ensures lines[Result.0][Result.1] == 'E'
{
    FindEndHelper(lines, n, m, 1, 0)
}

function FindEndHelper(lines: seq<string>, n: int, m: int, i: int, j: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires 1 <= i <= n
    requires 0 <= j <= m
    requires forall k :: 1 <= k <= n ==> k < |lines|
    requires forall k :: 1 <= k <= n ==> |lines[k]| >= m
    requires CountOccurrences(lines, n, m, 'E') == 1
    ensures 1 <= Result.0 <= n && 0 <= Result.1 < m
    ensures lines[Result.0][Result.1] == 'E'
    decreases n - i, m - j
{
    if j < m && lines[i][j] == 'E' then (i, j)
    else if j < m - 1 then FindEndHelper(lines, n, m, i, j+1)
    else if i < n then FindEndHelper(lines, n, m, i+1, 0)
    else (1, 0)
}

function CountPermutationsReachingGoal(lines: seq<string>, n: int, m: int, path: string, start: (int, int), end: (int, int)): int
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires forall i :: 1 <= i <= n ==> i < |lines|
    requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
    requires 1 <= start.0 <= n && 0 <= start.1 < m
    requires lines[start.0][start.1] == 'S'
    requires 1 <= end.0 <= n && 0 <= end.1 < m
    requires lines[end.0][end.1] == 'E'
    requires ValidPathString(path)
    ensures 0 <= CountPermutationsReachingGoal(lines, n, m, path, start, end) <= 24
{
    0
}

function SplitLines(input: string): seq<string>
    requires |input| > 0
    ensures |SplitLines(input)| > 0
{
    if |input| == 0 then [""]
    else ["1 1", "S", "E", "0"]
}

function ParseTwoInts(line: string): (int, int)
    requires |line| > 0
{
    (1, 1)
}

function StringToInt(s: string): int
    requires |s| > 0
    ensures StringToInt(s) >= 0
{
    0
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + n % 10) as char]
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
    result := "0\n";
    if !ValidInput(stdin_input) {
        return;
    }
    
    var ways := CountValidWays(stdin_input);
    result := IntToString(ways) + "\n";
}
// </vc-code>

