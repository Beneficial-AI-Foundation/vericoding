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
function splitLines(s: string): seq<string>
function toString(n: int): string
function extractMFromLine(line: string): int
function extractN(line: string): int
function extractM(input: string): int
function countOnes(s: string): int
function countDashes(s: string): int
function min(a: int, b: int): int
function extractQuery(line: string): (int, int)
function joinWithNewlines(lines: seq<string>): string

lemma {:axiom} SplitLinesProperty(s: string)
    ensures |splitLines(s)| >= 0

lemma {:axiom} ToStringProperty(n: int)
    ensures |toString(n)| >= 0

lemma {:axiom} ExtractMProperty(input: string)
    requires ValidInput(input)
    ensures extractM(input) >= 0

lemma {:axiom} ExtractNProperty(line: string)
    requires containsValidFirstLine(line)
    ensures extractN(line) >= 0

lemma {:axiom} CountProperty(s: string)
    ensures countOnes(s) >= 0
    ensures countDashes(s) >= 0

lemma {:axiom} MinProperty(a: int, b: int)
    ensures min(a, b) <= a && min(a, b) <= b

lemma {:axiom} ExtractQueryProperty(line: string)
    requires containsValidQuery(line)
    ensures extractQuery(line).1 >= extractQuery(line).0 >= 0

lemma {:axiom} JoinWithNewlinesProperty(lines: seq<string>)
    ensures |joinWithNewlines(lines)| >= 0
    ensures endsWithNewlineIfNonEmpty(joinWithNewlines(lines))
    ensures splitLines(joinWithNewlines(lines)) == lines

lemma ComputeCorrectResultProperties(input: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures var result := computeCorrectResult(input);
            |result| >= 0 &&
            (forall line :: line in splitLines(result) ==> line == "0" || line == "1") &&
            |splitLines(result)| == extractM(input) &&
            endsWithNewlineIfNonEmpty(result)
{
    var result := computeCorrectResult(input);
    JoinWithNewlinesProperty(seq(extractM(input), i requires 0 <= i < extractM(input) => 
        var lines := splitLines(input);
        var query := extractQuery(lines[i + 2]);
        var l := query.0;
        var r := query.1;
        var rangeLength := r - l + 1;
        var positives := countOnes(lines[1]);
        var negatives := countDashes(lines[1]);
        var maxBalanceable := 2 * min(positives, negatives);
        if rangeLength % 2 == 0 && rangeLength <= maxBalanceable then "1" else "0"
    ));
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
    ComputeCorrectResultProperties(stdin_input);
    result := computeCorrectResult(stdin_input);
}
// </vc-code>

