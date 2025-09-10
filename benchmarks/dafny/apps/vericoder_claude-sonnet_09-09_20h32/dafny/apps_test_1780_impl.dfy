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
{
    if |s| == 0 then []
    else splitLinesHelper(s, 0, 0, [])
}

function splitLinesHelper(s: string, start: int, pos: int, acc: seq<string>): seq<string>
    requires 0 <= start <= pos <= |s|
    decreases |s| - pos
{
    if pos == |s| then
        if start == pos then acc
        else acc + [s[start..pos]]
    else if s[pos] == '\n' then
        splitLinesHelper(s, pos + 1, pos + 1, acc + [s[start..pos]])
    else
        splitLinesHelper(s, start, pos + 1, acc)
}

function toString(n: int): string
    requires n >= 0
    ensures |toString(n)| > 0
    ensures forall i :: 0 <= i < |toString(n)| ==> '0' <= toString(n)[i] <= '9'
{
    if n == 0 then "0"
    else toStringHelper(n, "")
}

function toStringHelper(n: int, acc: string): string
    requires n >= 0
    ensures n > 0 ==> |toStringHelper(n, acc)| > |acc|
    ensures forall i :: 0 <= i < |toStringHelper(n, acc)| ==> '0' <= toStringHelper(n, acc)[i] <= '9'
    decreases n
{
    if n == 0 then acc
    else toStringHelper(n / 10, [('0' as int + n % 10) as char] + acc)
}

lemma ValidFirstLineHasSpace(line: string)
    requires containsValidFirstLine(line)
    ensures exists i :: 0 <= i < |line| && line[i] == ' '
{
    assert exists n, m :: n >= 0 && m >= 0 && line == toString(n) + " " + toString(m);
    var n, m :| n >= 0 && m >= 0 && line == toString(n) + " " + toString(m);
    var nStr := toString(n);
    assert |nStr| > 0;
    assert line[|nStr|] == ' ';
}

lemma ValidFirstLinePartsAreNumeric(line: string)
    requires containsValidFirstLine(line)
    ensures exists i :: 0 <= i < |line| && line[i] == ' '
    ensures var spacePos := findSpace(line); |line[0..spacePos]| > 0 && forall j {:trigger line[0..spacePos][j]} :: 0 <= j < |line[0..spacePos]| ==> '0' <= line[0..spacePos][j] <= '9'
    ensures var spacePos := findSpace(line); |line[spacePos + 1..]| > 0 && forall j {:trigger line[spacePos + 1..][j]} :: 0 <= j < |line[spacePos + 1..]| ==> '0' <= line[spacePos + 1..][j] <= '9'
{
    ValidFirstLineHasSpace(line);
    assert exists n, m :: n >= 0 && m >= 0 && line == toString(n) + " " + toString(m);
    var n, m :| n >= 0 && m >= 0 && line == toString(n) + " " + toString(m);
    var nStr := toString(n);
    var mStr := toString(m);
    var spacePos := findSpace(line);
    assert spacePos == |nStr|;
    assert line[0..spacePos] == nStr;
    assert line[spacePos + 1..] == mStr;
    assert |nStr| > 0;
    assert |mStr| > 0;
}

lemma ValidQueryHasSpace(line: string)
    requires containsValidQuery(line)
    ensures exists i :: 0 <= i < |line| && line[i] == ' '
{
    assert exists l, r :: l >= 0 && r >= l && line == toString(l) + " " + toString(r);
    var l, r :| l >= 0 && r >= l && line == toString(l) + " " + toString(r);
    var lStr := toString(l);
    assert |lStr| > 0;
    assert line[|lStr|] == ' ';
}

lemma ValidQueryPartsAreNumeric(line: string)
    requires containsValidQuery(line)
    ensures exists i :: 0 <= i < |line| && line[i] == ' '
    ensures var spacePos := findSpace(line); |line[0..spacePos]| > 0 && forall j {:trigger line[0..spacePos][j]} :: 0 <= j < |line[0..spacePos]| ==> '0' <= line[0..spacePos][j] <= '9'
    ensures var spacePos := findSpace(line); |line[spacePos + 1..]| > 0 && forall j {:trigger line[spacePos + 1..][j]} :: 0 <= j < |line[spacePos + 1..]| ==> '0' <= line[spacePos + 1..][j] <= '9'
{
    ValidQueryHasSpace(line);
    assert exists l, r :: l >= 0 && r >= l && line == toString(l) + " " + toString(r);
    var l, r :| l >= 0 && r >= l && line == toString(l) + " " + toString(r);
    var lStr := toString(l);
    var rStr := toString(r);
    var spacePos := findSpace(line);
    assert spacePos == |lStr|;
    assert line[0..spacePos] == lStr;
    assert line[spacePos + 1..] == rStr;
    assert |lStr| > 0;
    assert |rStr| > 0;
}

function extractN(line: string): int
    requires containsValidFirstLine(line)
{
    ValidFirstLineHasSpace(line);
    ValidFirstLinePartsAreNumeric(line);
    var spacePos := findSpace(line);
    parseInt(line[0..spacePos])
}

function extractM(input: string): int
    requires ValidInput(input)
{
    extractMFromLine(splitLines(input)[0])
}

function extractMFromLine(line: string): int
    requires containsValidFirstLine(line)
{
    ValidFirstLineHasSpace(line);
    ValidFirstLinePartsAreNumeric(line);
    var spacePos := findSpace(line);
    parseInt(line[spacePos + 1..])
}

function findSpace(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == ' '
    ensures 0 <= findSpace(s) < |s|
    ensures s[findSpace(s)] == ' '
{
    findSpaceHelper(s, 0)
}

function findSpaceHelper(s: string, pos: int): int
    requires 0 <= pos <= |s|
    requires exists i :: pos <= i < |s| && s[i] == ' '
    ensures pos <= findSpaceHelper(s, pos) < |s|
    ensures s[findSpaceHelper(s, pos)] == ' '
    decreases |s| - pos
{
    if pos < |s| && s[pos] == ' ' then pos
    else findSpaceHelper(s, pos + 1)
}

function parseInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    parseIntHelper(s, 0, 0)
}

function parseIntHelper(s: string, pos: int, acc: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s| - pos
{
    if pos == |s| then acc
    else parseIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
}

function countOnes(s: string): int
{
    countOnesHelper(s, 0, 0)
}

function countOnesHelper(s: string, pos: int, count: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos == |s| then count
    else if s[pos] == '1' then countOnesHelper(s, pos + 1, count + 1)
    else countOnesHelper(s, pos + 1, count)
}

function countDashes(s: string): int
{
    countDashesHelper(s, 0, 0)
}

function countDashesHelper(s: string, pos: int, count: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos == |s| then count
    else if s[pos] == '-' then countDashesHelper(s, pos + 1, count + 1)
    else countDashesHelper(s, pos + 1, count)
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function extractQuery(line: string): (int, int)
    requires containsValidQuery(line)
{
    ValidQueryHasSpace(line);
    ValidQueryPartsAreNumeric(line);
    var spacePos := findSpace(line);
    (parseInt(line[0..spacePos]), parseInt(line[spacePos + 1..]))
}

function joinWithNewlines(lines: seq<string>): string
    ensures endsWithNewlineIfNonEmpty(joinWithNewlines(lines))
{
    joinWithNewlinesHelper(lines, 0, "")
}

function joinWithNewlinesHelper(lines: seq<string>, pos: int, acc: string): string
    requires 0 <= pos <= |lines|
    ensures pos < |lines| ==> |joinWithNewlinesHelper(lines, pos, acc)| > |acc| && joinWithNewlinesHelper(lines, pos, acc)[|joinWithNewlinesHelper(lines, pos, acc)|-1] == '\n'
    ensures pos == |lines| ==> joinWithNewlinesHelper(lines, pos, acc) == acc
    decreases |lines| - pos
{
    if pos == |lines| then acc
    else joinWithNewlinesHelper(lines, pos + 1, acc + lines[pos] + "\n")
}

lemma JoinWithNewlinesCorrectness(outputs: seq<string>)
    ensures forall line :: line in splitLines(joinWithNewlines(outputs)) ==> line in outputs
    ensures |splitLines(joinWithNewlines(outputs))| == |outputs|
{
    if |outputs| == 0 {
        assert joinWithNewlines(outputs) == "";
        assert splitLines("") == [];
    } else {
        var result := joinWithNewlines(outputs);
        var split := splitLines(result);
        assert |split| == |outputs|;
        forall line | line in split
            ensures line in outputs
        {
        }
    }
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

    JoinWithNewlinesCorrectness(outputs);
    result := joinWithNewlines(outputs);
    
    assert result == computeCorrectResult(stdin_input);
    assert forall line :: line in splitLines(result) ==> line == "0" || line == "1";
    assert |splitLines(result)| == extractM(stdin_input);
}
// </vc-code>

