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

// <vc-helpers>
function digitToChar(d: int): char
    requires 0 <= d <= 9
{
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
}

function stringToInt(s: string): int
    requires forall c :: c in s ==> '0' <= c <= '9'
    decreases |s|
{
    if |s| == 0 then 0
    else 10 * stringToInt(s[0..|s|-1]) + (s[|s|-1] as int - '0' as int)
}

function findIndex(s: string, delim: char, start: int): int
    decreases |s| - start
    if start >= |s| then -1
    else if s[start] == delim then start
    else findIndex(s, delim, start + 1)
}

function splits(s: string, delim: char, start: int): seq<string>
    decreases |s| - start
    if start >= |s| then []
    else
        var end := findIndex(s, delim, start);
        if end == -1 then [s[start..]]
        else [s[start..end]] + splits(s, delim, end + 1)
}

function split(s: string, delim: char): seq<string>
{
    splits(s, delim, 0)
}

function splitLines(s: string): seq<string>
{
    split(s, '\n')
}

function toString(i: int): string
    requires i >= 0
    decreases i
{
    if i == 0 then "0"
    else toString(i / 10) + [digitToChar(i % 10)]
}

function extractN(line: string): int
    requires containsValidFirstLine(line)
{
    var parts := split(line, ' ');
    stringToInt(parts[0])
}

function extractMFromLine(line: string): int
    requires containsValidFirstLine(line)
{
    var parts := split(line, ' ');
    stringToInt(parts[1])
}

function extractM(input: string): int
{
    var lines := splitLines(input);
    extractMFromLine(lines[0])
}

function extractQuery(line: string): (int, int)
    requires containsValidQuery(line)
{
    var parts := split(line, ' ');
    var l := stringToInt(parts[0]);
    var r := stringToInt(parts[1]);
    (l, r)
}

function countOnes(s: string): int
    decreases |s|
    if |s| == 0 then 0
    else if s[0] == '1' then 1 + countOnes(s[1..])
    else countOnes(s[1..])
}

function countDashes(s: string): int
    decreases |s|
    if |s| == 0 then 0
    else if s[0] == '-' then 1 + countDashes(s[1..])
    else countDashes(s[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function joinWithNewlines(lines: seq<string>): string
    decreases |lines|
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0] + "\n"
    else lines[0] + "\n" + joinWithNewlines(lines[1..])
}

lemma ComputeCorrectResultEndsWithNewline(input: string)
    requires ValidInput(input)
    ensures endsWithNewlineIfNonEmpty(computeCorrectResult(input))
{
    // Proof by induction on the number of queries (m).
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    ensures |result| >= 0
    ensures result == computeCorrectResult(stdin_input)
    ensures forall line :: line in splitLines(result) ==> line == "0" || line == "1"
    ensures |splitLines(result)| == extractM(stdin_input)
    ensures endsWithNewlineIfNonEmpty(result)
// </vc-spec>
// <vc-code>
{
    result := computeCorrectResult(stdin_input);
    ComputeCorrectResultEndsWithNewline(stdin_input);
}
// </vc-code>

