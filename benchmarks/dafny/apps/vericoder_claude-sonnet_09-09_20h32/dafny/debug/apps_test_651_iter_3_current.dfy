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
function SplitLines(input: string): seq<string>
    ensures |SplitLines(input)| >= 1

function ParseTwoInts(line: string): (int, int)

function FindStart(lines: seq<string>, n: int, m: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0

function FindEnd(lines: seq<string>, n: int, m: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0

function CountOccurrences(lines: seq<string>, n: int, m: int, c: char): int
    requires |lines| >= n + 2
    requires n > 0 && m > 0

function CountPermutationsReachingGoal(lines: seq<string>, n: int, m: int, path: string, start: (int, int), end: (int, int)): int
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    ensures CountPermutationsReachingGoal(lines, n, m, path, start, end) >= 0
    ensures CountPermutationsReachingGoal(lines, n, m, path, start, end) <= 24

function StringToInt(s: string): int
    requires |s| > 0
    requires forall c :: c in s ==> '0' <= c <= '9'

function IntToString(n: int): string
    requires 0 <= n <= 24
    ensures |IntToString(n)| > 0
    ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
    ensures StringToInt(IntToString(n)) == n

lemma StringToIntProperties(s: string)
    requires |s| > 0
    requires forall c :: c in s ==> '0' <= c <= '9'
    ensures 0 <= StringToInt(s)

lemma ResultStringProperties(s: string)
    requires |s| > 0
    requires forall c :: c in s ==> ('0' <= c <= '9') || c == '\n'
    requires s[|s|-1] == '\n'
    requires |s| >= 2
    ensures forall c :: c in s[..|s|-1] ==> '0' <= c <= '9'
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
    if !ValidInput(stdin_input) {
        var result := "0\n";
        assert ValidResult(result);
        assert StringToInt(result[..|result|-1]) == 0;
        return result;
    }
    
    var count := CountValidWays(stdin_input);
    var countStr := IntToString(count);
    var result := countStr + "\n";
    
    assert ValidResult(result);
    StringToIntProperties(countStr);
    assert result[..|result|-1] == countStr;
    assert StringToInt(result[..|result|-1]) == count;
    
    return result;
}
// </vc-code>

