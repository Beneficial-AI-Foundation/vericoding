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
    splitLinesHelper(s, 0, 0)
}

function splitLinesHelper(s: string, start: nat, i: nat): seq<string>
    requires start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start == i then []
        else [s[start..i]]
    else if s[i] == '\n' then
        [s[start..i]] + splitLinesHelper(s, i+1, i+1)
    else
        splitLinesHelper(s, start, i+1)
}

function toString(n: nat): string
{
    if n == 0 then "0"
    else toStringHelper(n)
}

function toStringHelper(n: nat): string
    requires n > 0
    decreases n
{
    if n < 10 then [('0' as char) + n as char]
    else toStringHelper(n / 10) + [('0' as char) + (n % 10) as char]
}

function extractN(line: string): nat
{
    var parts := splitBySpace(line);
    if |parts| >= 1 then parseNat(parts[0]) else 0
}

function extractMFromLine(line: string): nat
{
    var parts := splitBySpace(line);
    if |parts| >= 2 then parseNat(parts[1]) else 0
}

function extractM(input: string): nat
    requires ValidInput(input)
{
    var lines := splitLines(input);
    extractMFromLine(lines[0])
}

function splitBySpace(s: string): seq<string>
{
    splitBySpaceHelper(s, 0, 0)
}

function splitBySpaceHelper(s: string, start: nat, i: nat): seq<string>
    requires start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start == i then []
        else [s[start..i]]
    else if s[i] == ' ' then
        if start == i then splitBySpaceHelper(s, i+1, i+1)
        else [s[start..i]] + splitBySpaceHelper(s, i+1, i+1)
    else
        splitBySpaceHelper(s, start, i+1)
}

function parseNat(s: string): nat
{
    if |s| == 0 then 0
    else parseNatHelper(s, 0, 0)
}

function parseNatHelper(s: string, i: nat, acc: nat): nat
    requires i <= |s|
    decreases |s| - i
{
    if i == |s| then acc
    else if '0' <= s[i] <= '9' then
        parseNatHelper(s, i+1, acc * 10 + (s[i] - '0') as nat)
    else acc
}

function countOnes(s: string): nat
{
    if |s| == 0 then 0
    else (if s[0] == '1' then 1 else 0) + countOnes(s[1..])
}

function countDashes(s: string): nat
{
    if |s| == 0 then 0
    else (if s[0] == '-' then 1 else 0) + countDashes(s[1..])
}

function min(a: nat, b: nat): nat
{
    if a <= b then a else b
}

function extractQuery(line: string): (nat, nat)
{
    var parts := splitBySpace(line);
    if |parts| >= 2 then
        (parseNat(parts[0]), parseNat(parts[1]))
    else
        (0, 0)
}

function joinWithNewlines(lines: seq<string>): string
    ensures |lines| > 0 ==> endsWithNewlineIfNonEmpty(joinWithNewlines(lines))
    ensures |lines| == 0 ==> joinWithNewlines(lines) == ""
    ensures splitLines(joinWithNewlines(lines)) == lines
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0] + "\n"
    else lines[0] + "\n" + joinWithNewlines(lines[1..])
}

method ParseFirstLine(line: string) returns (n: nat, m: nat)
    ensures n >= 0 && m >= 0
    ensures n == extractN(line)
    ensures m == extractMFromLine(line)
{
    var parts := SplitBySpaceMethod(line);
    if |parts| >= 2 {
        n := ParseNatMethod(parts[0]);
        m := ParseNatMethod(parts[1]);
    } else if |parts| == 1 {
        n := ParseNatMethod(parts[0]);
        m := 0;
    } else {
        n := 0;
        m := 0;
    }
}

method SplitBySpaceMethod(s: string) returns (parts: seq<string>)
    ensures parts == splitBySpace(s)
{
    parts := [];
    var start := 0;
    var i := 0;
    while i < |s|
    {
        if s[i] == ' ' {
            if start < i {
                parts := parts + [s[start..i]];
            }
            start := i + 1;
        }
        i := i + 1;
    }
    if start < |s| {
        parts := parts + [s[start..|s|]];
    }
}

method ParseNatMethod(s: string) returns (n: nat)
    ensures n == parseNat(s)
{
    n := 0;
    var i := 0;
    while i < |s| && '0' <= s[i] <= '9'
    {
        n := n * 10 + (s[i] - '0') as nat;
        i := i + 1;
    }
}

lemma CountOnesLemma(s: string, i: nat)
    requires 0 <= i < |s|
    ensures countOnes(s[..i+1]) == countOnes(s[..i]) + (if s[i] == '1' then 1 else 0)
{
    assert s[..i+1] == s[..i] + [s[i]];
    calc {
        countOnes(s[..i+1]);
        == countOnes(s[..i] + [s[i]]);
        == { CountOnesAppend(s[..i], [s[i]]); }
        countOnes(s[..i]) + countOnes([s[i]]);
        == countOnes(s[..i]) + (if s[i] == '1' then 1 else 0);
    }
}

lemma CountOnesAppend(s1: string, s2: string)
    ensures countOnes(s1 + s2) == countOnes(s1) + countOnes(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        calc {
            countOnes(s1 + s2);
            == (if (s1 + s2)[0] == '1' then 1 else 0) + countOnes((s1 + s2)[1..]);
            == { assert (s1 + s2)[0] == s1[0]; assert (s1 + s2)[1..] == s1[1..] + s2; }
            (if s1[0] == '1' then 1 else 0) + countOnes(s1[1..] + s2);
            == { CountOnesAppend(s1[1..], s2); }
            (if s1[0] == '1' then 1 else 0) + countOnes(s1[1..]) + countOnes(s2);
            == countOnes(s1) + countOnes(s2);
        }
    }
}

lemma CountDashesLemma(s: string, i: nat)
    requires 0 <= i < |s|
    ensures countDashes(s[..i+1]) == countDashes(s[..i]) + (if s[i] == '-' then 1 else 0)
{
    assert s[..i+1] == s[..i] + [s[i]];
    calc {
        countDashes(s[..i+1]);
        == countDashes(s[..i] + [s[i]]);
        == { CountDashesAppend(s[..i], [s[i]]); }
        countDashes(s[..i]) + countDashes([s[i]]);
        == countDashes(s[..i]) + (if s[i] == '-' then 1 else 0);
    }
}

lemma CountDashesAppend(s1: string, s2: string)
    ensures countDashes(s1 + s2) == countDashes(s1) + countDashes(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        calc {
            countDashes(s1 + s2);
            == (if (s1 + s2)[0] == '-' then 1 else 0) + countDashes((s1 + s2)[1..]);
            == { assert (s1 + s2)[0] == s1[0]; assert (s1 + s2)[1..] == s1[1..] + s2; }
            (if s1[0] == '-' then 1 else 0) + countDashes(s1[1..] + s2);
            == { CountDashesAppend(s1[1..], s2); }
            (if s1[0] == '-' then 1 else 0) + countDashes(s1[1..]) + countDashes(s2);
            == countDashes(s1) + countDashes(s2);
        }
    }
}

method CountOnesAndDashes(s: string) returns (ones: nat, dashes: nat)
    ensures ones == countOnes(s)
    ensures dashes == countDashes(s)
{
    ones := 0;
    dashes := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant ones == countOnes(s[..i])
        invariant dashes == countDashes(s[..i])
    {
        if s[i] == '1' {
            ones := ones + 1;
        } else if s[i] == '-' {
            dashes := dashes + 1;
        }
        i := i + 1;
        if i > 0 {
            CountOnesLemma(s, i-1);
            CountDashesLemma(s, i-1);
        }
    }
    assert s[..i] == s;
}

method SplitLinesMethod(s: string) returns (lines: seq<string>)
    ensures lines == splitLines(s)
{
    lines := [];
    var start := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant start == 0 || s[start-1] == '\n'
        invariant forall j :: 0 <= j < |lines| ==> 
            lines[j] in splitLines(s[..i])
    {
        if s[i] == '\n' {
            lines := lines + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    if start < |s| {
        lines := lines + [s[start..|s|]];
    }
}

method ParseQuery(line: string) returns (l: nat, r: nat)
    ensures (l, r) == extractQuery(line)
{
    var parts := SplitBySpaceMethod(line);
    if |parts| >= 2 {
        l := ParseNatMethod(parts[0]);
        r := ParseNatMethod(parts[1]);
    } else {
        l := 0;
        r := 0;
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
    var lines := SplitLinesMethod(stdin_input);
    
    var n, m := ParseFirstLine(lines[0]);
    
    var arrayLine := lines[1];
    var positives, negatives := CountOnesAndDashes(arrayLine);
    var maxBalanceable := 2 * min(positives, negatives);
    
    ghost var spec := computeCorrectResult(stdin_input);
    ghost var expectedOutputs := seq(m, j requires 0 <= j < m => 
        var query := extractQuery(lines[j + 2]);
        var l := query.0;
        var r := query.1;
        var rangeLength := r - l + 1;
        if rangeLength % 2 == 0 && rangeLength <= maxBalanceable then "1" else "0"
    );
    
    var outputs: seq<string> := [];
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant |outputs| == i
        invariant outputs == expectedOutputs[..i]
    {
        var l, r := ParseQuery(lines[i + 2]);
        var rangeLength: int := (r as int) - (l as int) + 1;
        
        if rangeLength > 0 && rangeLength % 2 == 0 && rangeLength <= maxBalanceable as int {
            outputs := outputs + ["1"];
        } else {
            outputs := outputs + ["0"];
        }
        i := i + 1;
    }
    
    result := joinWithNewlines(outputs);
}
// </vc-code>

