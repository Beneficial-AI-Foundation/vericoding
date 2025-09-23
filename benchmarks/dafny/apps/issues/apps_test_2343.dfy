// <vc-preamble>
predicate ValidInputFormat(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 2 && 
    IsValidPositiveInteger(lines[0]) &&
    (var t := StringToInt(lines[0]);
     t >= 1 && t <= 1000 && |lines| >= t + 1 &&
     forall i :: 1 <= i <= t && i < |lines| ==> ValidTestCaseLine(lines[i]))
}

predicate ValidTestCaseLine(line: string)
{
    var parts := SplitOnSpace(line);
    |parts| == 2 && 
    IsValidPositiveInteger(parts[0]) && IsValidPositiveInteger(parts[1]) &&
    (var n := StringToInt(parts[0]); var k := StringToInt(parts[1]);
     1 <= n <= 1000000000 && 1 <= k <= 1000000000000000000)
}

predicate ValidOutputFormat(output: string)
{
    var lines := SplitLines(output);
    forall line :: line in lines && line != "" ==> 
        (line == "NO" || 
         (|line| >= 5 && line[..4] == "YES " && 
          var logValStr := line[4..];
          IsValidNonNegativeInteger(logValStr)))
}

predicate OutputMatchesInputCount(input: string, output: string)
{
    var inputLines := SplitLines(input);
    var outputLines := SplitLines(output);
    |inputLines| >= 1 && IsValidPositiveInteger(inputLines[0]) &&
    (var t := StringToInt(inputLines[0]);
     CountNonEmptyLines(outputLines) == t)
}

predicate ValidTestCase(n: int, k: int)
{
    1 <= n <= 1000000000 && 1 <= k <= 1000000000000000000
}

predicate TestCaseInInput(input: string, n: int, k: int)
{
    var lines := SplitLines(input);
    exists i :: 1 <= i < |lines| && 
        var parts := SplitOnSpace(lines[i]);
        |parts| == 2 && StringToInt(parts[0]) == n && StringToInt(parts[1]) == k
}

predicate ValidGridSplittingResult(n: int, k: int, output: string)
    requires ValidTestCase(n, k)
{
    if n == 1 then
        (k == 1 && output == "YES 0") || (k != 1 && output == "NO")
    else if n == 2 then
        (k <= 2 && output == "YES 1") ||
        (k > 2 && k != 3 && k <= 5 && output == "YES 0") ||
        ((k == 3 || k > 5) && output == "NO")
    else
        var foundResult := FindValidLevelResult(n, k);
        if foundResult.found then
            |output| >= 5 && output[..4] == "YES " && 
            var logValStr := output[4..];
            IsValidNonNegativeInteger(logValStr) &&
            var logVal := StringToInt(logValStr);
            logVal == foundResult.level
        else
            var maxPossible := GetMaxSplits(n);
            if k <= maxPossible then
                output == "YES 0"
            else
                output == "NO"
}

predicate IsValidPositiveInteger(s: string)
{
    |s| > 0 && s != "0" && forall c :: c in s ==> '0' <= c <= '9'
}

predicate IsValidNonNegativeInteger(s: string)
{
    |s| > 0 && forall c :: c in s ==> '0' <= c <= '9'
}

function StringToInt(s: string): int
    requires IsValidPositiveInteger(s) || IsValidNonNegativeInteger(s)
{
    0
}

function SplitLines(s: string): seq<string>
{
    [""]
}

function SplitOnSpace(s: string): seq<string>
{
    [""]
}

function GetCorrespondingOutput(output: string, n: int, k: int): string
{
    var lines := SplitLines(output);
    if |lines| > 0 then lines[0] else ""
}
// </vc-preamble>

// <vc-helpers>
datatype LevelResult = LevelResult(found: bool, level: int)

function GetMaxSplits(n: int): int
    requires n >= 1
{
    GetMaxSplitsHelper(n, 0)
}

function GetMaxSplitsHelper(remaining: int, ans: int): int
    requires remaining >= 0
    decreases remaining
{
    if remaining == 0 then
        ans
    else
        var newAns := 4 * ans + 1;
        if newAns > 10000000000000000000 then
            ans
        else
            GetMaxSplitsHelper(remaining - 1, newAns)
}

function FindValidLevelResult(n: int, k: int): LevelResult
    requires n >= 3
{
    FindValidLevelHelper(n - 1, 1, 3, k)
}

function FindValidLevelHelper(siz: int, l: int, cnt: int, k: int): LevelResult
    decreases siz
{
    if siz <= 0 then
        LevelResult(false, 0)
    else if l <= k < l + cnt then
        LevelResult(true, siz)
    else
        FindValidLevelHelper(siz - 1, l + cnt, 2 * cnt + 1, k)
}

function CountNonEmptyLines(lines: seq<string>): int
{
    if |lines| == 0 then 0
    else if lines[0] == "" then CountNonEmptyLines(lines[1..])
    else 1 + CountNonEmptyLines(lines[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    ensures ValidOutputFormat(result)
    ensures OutputMatchesInputCount(stdin_input, result)
    ensures forall n, k :: ValidTestCase(n, k) && TestCaseInInput(stdin_input, n, k) ==>
        ValidGridSplittingResult(n, k, GetCorrespondingOutput(result, n, k))
    ensures result != ""
// </vc-spec>
// <vc-code>
{
    result := "";
}
// </vc-code>
