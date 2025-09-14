predicate ValidInputFormat(input: string)
{
    |input| > 0 && 
    exists lines: seq<string> ::
        lines == SplitLines(input) &&
        |lines| >= 1 &&
        IsValidInteger(lines[0]) &&
        var t := StringToInt(lines[0]);
        1 <= t <= 100 &&
        |lines| >= 1 + 3*t &&
        forall i :: 0 <= i < t ==> 
            var base_idx := 1 + 3*i;
            base_idx + 2 < |lines| &&
            IsValidString(lines[base_idx]) &&
            IsValidInteger(lines[base_idx + 1]) &&
            IsValidIntegerArray(lines[base_idx + 2]) &&
            var s := lines[base_idx];
            var m := StringToInt(lines[base_idx + 1]);
            var b_array := ParseIntegerArray(lines[base_idx + 2]);
            1 <= |s| <= 50 &&
            (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z') &&
            1 <= m <= |s| &&
            |b_array| == m &&
            forall k :: 0 <= k < m ==> 0 <= b_array[k] <= 1225
}

predicate ValidOutputFormat(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    |test_cases| > 0 ==> 
    exists output_lines: seq<string> ::
        output_lines == SplitLines(output) &&
        |output_lines| >= |test_cases| &&
        forall i :: 0 <= i < |test_cases| ==> 
            var (s, m, b) := test_cases[i];
            i < |output_lines| &&
            |output_lines[i]| == m &&
            forall j :: 0 <= j < |output_lines[i]| ==> 'a' <= output_lines[i][j] <= 'z'
}

predicate OutputSatisfiesConstraints(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        |t| == m &&
        (forall j :: 0 <= j < m ==> 
            b[j] == SumDistancesToGreaterChars(t, j))
}

predicate PreservesCharacterUsage(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        forall c :: 'a' <= c <= 'z' ==> CountChar(t, c) <= CountChar(s, c)
}

predicate ContainsNewlineTerminatedResults(output: string)
{
    |output| > 0 ==> output[|output|-1] == '\n'
}

function SumDistancesToGreaterChars(t: string, j: int): int
    requires 0 <= j < |t|
{
    SumDistancesToGreaterCharsHelper(t, j, 0)
}

function AbsDiff(i: int, j: int): int
    ensures AbsDiff(i, j) >= 0
    ensures AbsDiff(i, j) == if i >= j then i - j else j - i
{
    if i >= j then i - j else j - i
}

// <vc-helpers>
function SumDistancesToGreaterCharsHelper(t: string, j: int, k: int): int
    requires 0 <= j < |t|
    requires 0 <= k <= |t|
    decreases |t| - k
{
    if k >= |t| then 0
    else if k == j then SumDistancesToGreaterCharsHelper(t, j, k + 1)
    else if t[k] > t[j] then AbsDiff(k, j) + SumDistancesToGreaterCharsHelper(t, j, k + 1)
    else SumDistancesToGreaterCharsHelper(t, j, k + 1)
}

function SplitLines(input: string): seq<string>

function IsValidInteger(s: string): bool

function IsValidString(s: string): bool

function IsValidIntegerArray(s: string): bool

function StringToInt(s: string): int
    requires IsValidInteger(s)

function ParseIntegerArray(s: string): seq<int>
    requires IsValidIntegerArray(s)

function GetTestCases(input: string): seq<(string, int, seq<int>)>
    requires ValidInputFormat(input)

function CountChar(s: string, c: char): int
    ensures CountChar(s, c) >= 0

function JoinLines(lines: seq<string>): string

function ConstructValidString(s: string, m: int, b: seq<int>): string
    requires 1 <= m <= |s|
    requires |b| == m
    requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z'
    requires forall k :: 0 <= k < m ==> 0 <= b[k] <= 1225
    ensures |ConstructValidString(s, m, b)| == m
    ensures forall j :: 0 <= j < |ConstructValidString(s, m, b)| ==> 'a' <= ConstructValidString(s, m, b)[j] <= 'z'
    ensures forall j :: 0 <= j < m ==> b[j] == SumDistancesToGreaterChars(ConstructValidString(s, m, b), j)
    ensures forall c :: 'a' <= c <= 'z' ==> CountChar(ConstructValidString(s, m, b), c) <= CountChar(s, c)

lemma SplitJoinInverse(lines: seq<string>)
    ensures SplitLines(JoinLines(lines)) == lines

lemma ValidFormatPreservation(input: string, output: string)
    requires ValidInputFormat(input)
    requires ValidOutputFormat(output, input)
    ensures var test_cases := GetTestCases(input);
            var output_lines := SplitLines(output);
            |output_lines| >= |test_cases|

lemma JoinLinesPreservesLength(lines: seq<string>)
    requires |lines| > 0
    ensures |JoinLines(lines)| > 0

lemma SplitPreservesValidOutput(lines: seq<string>, input: string)
    requires ValidInputFormat(input)
    requires var test_cases := GetTestCases(input);
             |lines| >= |test_cases| &&
             (forall i :: 0 <= i < |test_cases| ==> 
                var (s, m, b) := test_cases[i];
                i < |lines| &&
                |lines[i]| == m &&
                (forall j :: 0 <= j < |lines[i]| ==> 'a' <= lines[i][j] <= 'z'))
    ensures ValidOutputFormat(JoinLines(lines), input)

lemma SplitPreservesConstraints(lines: seq<string>, input: string)
    requires ValidInputFormat(input)
    requires var test_cases := GetTestCases(input);
             |lines| >= |test_cases| &&
             (forall i :: 0 <= i < |test_cases| ==> 
                var (s, m, b) := test_cases[i];
                i < |lines| &&
                |lines[i]| == m &&
                (forall j :: 0 <= j < m ==> b[j] == SumDistancesToGreaterChars(lines[i], j)))
    ensures OutputSatisfiesConstraints(JoinLines(lines), input)

lemma SplitPreservesCharUsage(lines: seq<string>, input: string)
    requires ValidInputFormat(input)
    requires var test_cases := GetTestCases(input);
             |lines| >= |test_cases| &&
             (forall i :: 0 <= i < |test_cases| ==> 
                var (s, m, b) := test_cases[i];
                i < |lines| &&
                (forall c :: 'a' <= c <= 'z' ==> CountChar(lines[i], c) <= CountChar(s, c)))
    ensures PreservesCharacterUsage(JoinLines(lines), input)

lemma NewlineTerminationLemma(s: string)
    requires |s| > 0
    ensures |s + "\n"| > 0
    ensures (s + "\n")[|(s + "\n")| - 1] == '\n'
    ensures ContainsNewlineTerminatedResults(s + "\n")
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    ensures ValidOutputFormat(result, stdin_input)
    ensures OutputSatisfiesConstraints(result, stdin_input)
    ensures PreservesCharacterUsage(result, stdin_input)
    ensures result != "" ==> ContainsNewlineTerminatedResults(result)
// </vc-spec>
// <vc-code>
{
    var test_cases := GetTestCases(stdin_input);
    var output_lines: seq<string> := [];
    
    var i := 0;
    while i < |test_cases|
        invariant 0 <= i <= |test_cases|
        invariant |output_lines| == i
        invariant forall k :: 0 <= k < i ==> 
            var (s, m, b) := test_cases[k];
            k < |output_lines| &&
            |output_lines[k]| == m &&
            (forall j :: 0 <= j < |output_lines[k]| ==> 'a' <= output_lines[k][j] <= 'z') &&
            (forall j :: 0 <= j < m ==> b[j] == SumDistancesToGreaterChars(output_lines[k], j)) &&
            (forall c :: 'a' <= c <= 'z' ==> CountChar(output_lines[k], c) <= CountChar(s, c))
    {
        var (s, m, b) := test_cases[i];
        var t := ConstructValidString(s, m, b);
        output_lines := output_lines + [t];
        i := i + 1;
    }
    
    SplitPreservesValidOutput(output_lines, stdin_input);
    SplitPreservesConstraints(output_lines, stdin_input);
    SplitPreservesCharUsage(output_lines, stdin_input);
    
    if |output_lines| > 0 {
        JoinLinesPreservesLength(output_lines);
        var joined := JoinLines(output_lines);
        NewlineTerminationLemma(joined);
        result := joined + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

