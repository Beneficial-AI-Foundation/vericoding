Given an array of n integers (each either -1 or 1), determine for each query 
whether the array can be rearranged so that the sum of elements in a given 
range equals 0. A range can sum to 0 only if it has even length and we have 
enough positive and negative values to fill half the positions each.

ghost predicate ValidInput(input: string)
{
    var lines := splitLines(input);
    |lines| >= 2 &&
    containsValidFirstLine(lines[0]) &&
    containsValidSecondLine(lines[1]) &&
    |lines| == 2 + extractMFromLine(lines[0]) &&
    (forall i :: 2 <= i < |lines| ==> containsValidQuery(lines[i])) &&
    extractN(lines[0]) == |lines[1]|
}

ghost predicate containsValidFirstLine(line: string)
{
    exists n, m :: n >= 0 && m >= 0 && line == toString(n) + " " + toString(m)
}

ghost predicate containsValidSecondLine(line: string)
{
    |line| >= 0 &&
    forall c :: c in line ==> c == '1' || c == '-'
}

ghost predicate containsValidQuery(line: string)
{
    exists l, r :: l >= 0 && r >= l && line == toString(l) + " " + toString(r)
}

function computeCorrectResult(input: string): string
    requires |input| > 0
    requires ValidInput(input)
    ensures |computeCorrectResult(input)| >= 0
    ensures forall line :: line in splitLines(computeCorrectResult(input)) ==> line == "0" || line == "1"
    ensures |splitLines(computeCorrectResult(input))| == extractM(input)
{
    var lines := splitLines(input);
    var firstLine := lines[0];
    var n := extractN(firstLine);
    var m := extractM(input);
    var arrayLine := lines[1];
    var positives := countOnes(arrayLine);
    var negatives := countDashes(arrayLine);
    var maxBalanceable := 2 * min(positives, negatives);

    var outputs := seq(m, i requires 0 <= i < m => 
        var query := extractQuery(lines[i + 2]);
        var l := query.0;
        var r := query.1;
        var rangeLength := r - l + 1;
        if rangeLength % 2 == 0 && rangeLength <= maxBalanceable then "1" else "0"
    );

    joinWithNewlines(outputs)
}

predicate endsWithNewlineIfNonEmpty(s: string)
{
    |s| == 0 || (|s| > 0 && s[|s|-1] == '\n')
}

function extractN(firstLine: string): int
    requires containsValidFirstLine(firstLine)
    ensures extractN(firstLine) >= 0
{
    0  // placeholder
}

function extractM(input: string): int
    requires ValidInput(input)
    ensures extractM(input) >= 0
{
    var lines := splitLines(input);
    extractMFromLine(lines[0])
}

function extractMFromLine(firstLine: string): int
    requires containsValidFirstLine(firstLine)
    ensures extractMFromLine(firstLine) >= 0
{
    0  // placeholder
}

function countOnes(s: string): int
    ensures countOnes(s) >= 0
    ensures countOnes(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == '1' then 1 else 0) + countOnes(s[1..])
}

function countDashes(s: string): int
    ensures countDashes(s) >= 0  
    ensures countDashes(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == '-' then 1 else 0) + countDashes(s[1..])
}

function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a <= b then a else b
}

function extractQuery(line: string): (int, int)
    requires containsValidQuery(line)
    ensures extractQuery(line).0 >= 0
    ensures extractQuery(line).1 >= extractQuery(line).0
{
    (0, 0)  // placeholder
}

function splitLines(s: string): seq<string>
    ensures |splitLines(s)| >= 0
{
    []  // placeholder
}

function joinWithNewlines(lines: seq<string>): string
    ensures |joinWithNewlines(lines)| >= 0
{
    ""  // placeholder
}

function toString(n: int): string
    ensures |toString(n)| >= 0
{
    ""  // placeholder
}

method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    ensures |result| >= 0
    ensures result == computeCorrectResult(stdin_input)
    ensures forall line :: line in splitLines(result) ==> line == "0" || line == "1"
    ensures |splitLines(result)| == extractM(stdin_input)
    ensures endsWithNewlineIfNonEmpty(result)
{
    var lines := splitLines(stdin_input);
    var firstLine := lines[0];
    var n := extractN(firstLine);
    var m := extractM(stdin_input);
    var arrayLine := lines[1];
    var positives := countOnes(arrayLine);
    var negatives := countDashes(arrayLine);
    var maxBalanceable := 2 * min(positives, negatives);

    var outputs := seq(m, i requires 0 <= i < m => 
        var query := extractQuery(lines[i + 2]);
        var l := query.0;
        var r := query.1;
        var rangeLength := r - l + 1;
        if rangeLength % 2 == 0 && rangeLength <= maxBalanceable then "1" else "0"
    );

    result := joinWithNewlines(outputs);
}
