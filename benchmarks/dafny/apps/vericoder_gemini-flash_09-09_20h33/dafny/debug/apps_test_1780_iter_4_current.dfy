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
    ensures forall i :: 0 <= i < |splitLines(s)| ==> |splitLines(s)[i]| >= 0
{
    if s == "" then
        []
    else if s.Contains('\n') then
        var firstLine := s.Substring(0, s.IndexOf('\n'));
        var rest := s.Substring(s.IndexOf('\n') + 1);
        [firstLine] + splitLines(rest)
    else
        [s]
}

function toString(i: int): string
    ensures |toString(i)| >= 1
    ensures i >= 0 ==> (forall k :: 0 <= k < |toString(i)| ==> '0' <= toString(i)[k] <= '9')
{
    if i == 0 then
        "0"
    else if i < 0 then
        "-" + toString(-i)
    else
        var s := "";
        var k_var := i; // Renamed 'k' to 'k_var'
        while k_var > 0
            invariant k_var >= 0
            invariant forall c :: c in s ==> '0' <= c <= '9'
            decreases k_var
        {
            s := (k_var % 10).ToString() + s;
            k_var := k_var / 10;
        }
        s
}

function extractNFromLine(line: string): int
    requires containsValidFirstLine(line)
{
    var parts := split(line, ' ');
    assert |parts| == 2;
    var n_str := parts[0];
    (n_str as int)
}

function extractMFromLine(line: string): int
    requires containsValidFirstLine(line)
{
    var parts := split(line, ' ');
    assert |parts| == 2;
    var m_str := parts[1];
    (m_str as int)
}

function extractN(input: string): int
    requires ValidInput(input)
{
    extractNFromLine(splitLines(input)[0])
}

function extractM(input: string): int
    requires ValidInput(input)
{
    extractMFromLine(splitLines(input)[0])
}

function countOnes(s: string): int
    requires forall c :: c in s ==> c == '1' || c == '-'
    ensures countOnes(s) >= 0
{
    if s == "" then
        0
    else if s[0] == '1' then
        1 + countOnes(s.Substring(1))
    else
        countOnes(s.Substring(1))
}

function countDashes(s: string): int
    requires forall c :: c in s ==> c == '1' || c == '-'
    ensures countDashes(s) >= 0
{
    if s == "" then
        0
    else if s[0] == '-' then
        1 + countDashes(s.Substring(1))
    else
        countDashes(s.Substring(1))
}

function extractQuery(line: string): (int, int)
    requires containsValidQuery(line)
{
    var parts := split(line, ' ');
    assert |parts| == 2;
    var l_str := parts[0];
    var r_str := parts[1];
    (l_str as int, r_str as int)
}

function split(s: string, separator: char): seq<string>
    ensures forall i :: 0 <= i < |split(s, separator)| ==> |split(s, separator)[i]| >= 0
{
    if s == "" then
        []
    else if s.Contains(separator) then
        var firstPart := s.Substring(0, s.IndexOf(separator));
        var rest := s.Substring(s.IndexOf(separator) + 1);
        [firstPart] + split(rest, separator)
    else
        [s]
}

function joinWithNewlines(lines: seq<string>): string
    ensures |joinWithNewlines(lines)| >= 0
    ensures |lines| > 0 ==> endsWithNewlineIfNonEmpty(joinWithNewlines(lines))
{
    if |lines| == 0 then
        ""
    else if |lines| == 1 then
        lines[0] + "\n"
    else
        lines[0] + "\n" + joinWithNewlines(lines[1..])
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
    var lines := splitLines(stdin_input);
    var firstLine := lines[0];
    var m := extractMFromLine(firstLine);
    var arrayLine := lines[1];
    var positives := countOnes(arrayLine);
    var negatives := countDashes(arrayLine);
    var maxBalanceable := 2 * (if positives < negatives then positives else negatives);

    var outputs := seq(m, i => {
        var query := extractQuery(lines[i + 2]);
        var l := query.0;
        var r := query.1;
        var rangeLength := r - l + 1;
        if rangeLength % 2 == 0 && rangeLength <= maxBalanceable then "1" else "0"
    });

    result := joinWithNewlines(outputs);
}
// </vc-code>

