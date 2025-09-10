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
ghost function splitLines(s: string): seq<string>
    ensures |splitLines(s)| >= 1
    ensures forall i :: 0 <= i < |splitLines(s)| ==> |splitLines(s)[i]| >= 0
    ensures s == joinWithNewlines(splitLines(s))

ghost function extractN(line: string): nat
    requires containsValidFirstLine(line)

ghost function extractM(input: string): nat
    requires ValidInput(input)

ghost function extractMFromLine(line: string): nat
    requires containsValidFirstLine(line)

ghost function extractQuery(line: string): (nat, nat)
    requires containsValidQuery(line)

ghost function countOnes(s: string): nat
    ensures countOnes(s) >= 0

ghost function countDashes(s: string): nat
    ensures countDashes(s) >= 0

ghost function joinWithNewlines(lines: seq<string>): string
    ensures |joinWithNewlines(lines)| == 0 || joinWithNewlines(lines)[|joinWithNewlines(lines)|-1] == '\n'
    ensures |splitLines(joinWithNewlines(lines))| == |lines|

ghost lemma ValidInputImpliesLength(input: string)
    requires ValidInput(input)
    ensures |splitLines(input)| >= 2

ghost lemma QueryIndicesValid(input: string)
    requires ValidInput(input)
    ensures forall i :: 2 <= i < |splitLines(input)| ==> containsValidQuery(splitLines(input)[i])

ghost lemma SecondLineValid(input: string)
    requires ValidInput(input)
    ensures containsValidSecondLine(splitLines(input)[1])

ghost lemma FirstLineValid(input: string)
    requires ValidInput(input)
    ensures containsValidFirstLine(splitLines(input)[0])

ghost lemma ExtractMCorrect(input: string)
    requires ValidInput(input)
    ensures extractM(input) == extractMFromLine(splitLines(input)[0])

ghost lemma ExtractNCorrect(input: string)
    requires ValidInput(input)
    ensures extractN(splitLines(input)[0]) == |splitLines(input)[1]|

ghost lemma QueryExtractionCorrect(line: string)
    requires containsValidQuery(line)
    ensures var (l, r) := extractQuery(line); l >= 0 && r >= l
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
    var input_lines := splitLines(stdin_input);
    var firstLine := input_lines[0];
    var n := extractN(firstLine);
    var m := extractM(stdin_input);
    var arrayLine := input_lines[1];
    var positives := countOnes(arrayLine);
    var negatives := countDashes(arrayLine);
    var maxBalanceable := 2 * min(positives, negatives);

    var output_lines := [];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |output_lines| == i
        invariant forall j :: 0 <= j < i ==> output_lines[j] == "0" || output_lines[j] == "1"
    {
        var query_line := input_lines[i + 2];
        var query := extractQuery(query_line);
        var l := query.0;
        var r := query.1;
        var rangeLength := r - l + 1;
        var result_line := if rangeLength % 2 == 0 && rangeLength <= maxBalanceable then "1" else "0";
        output_lines := output_lines + [result_line];
        i := i + 1;
    }
    
    result := joinWithNewlines(output_lines);
}
// </vc-code>

