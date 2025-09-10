ghost predicate ValidInputFormat(s: string) {
    var lines := SplitLines(s);
    |lines| >= 1 &&
    exists n: nat, k: nat :: 
        ParsesAsIntegers(lines[0], n as int, k as int) && n > 0 && k > 0 && |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n && i < |lines| ==> 
            exists a: int, b: int :: ParsesAsIntegers(lines[i], a, b))
}

ghost predicate ParsedCorrectly(input: string, n: nat, k: nat, segments: seq<(int, int)>) {
    var lines := SplitLines(input);
    |lines| >= n + 1 && |segments| == n &&
    ParsesAsIntegers(lines[0], n as int, k as int) &&
    (forall i :: 0 <= i < n && i + 1 < |lines| ==> 
        ParsesAsIntegers(lines[i + 1], segments[i].0, segments[i].1))
}

predicate IsValidOutput(s: string) {
    |s| > 0 && s[|s| - 1] == '\n' && 
    (forall i :: 0 <= i < |s| - 1 ==> s[i] != '\n') &&
    IsNumericOutput(s[..|s| - 1])
}

function MinMovesToDivisible(segments: seq<(int, int)>, k: nat): nat
    requires k > 0
    ensures MinMovesToDivisible(segments, k) < k
{
    var totalCoverage := TotalCoverage(segments);
    var remainder := totalCoverage % k;
    if remainder == 0 then 0 else k - remainder
}

function TotalCoverage(segments: seq<(int, int)>): nat {
    if |segments| == 0 then 0
    else SegmentLength(segments[0]) + TotalCoverage(segments[1..])
}

function SegmentLength(segment: (int, int)): nat
    ensures SegmentLength(segment) >= 1
{
    var maxVal := MaxInt(segment.0, segment.1);
    var minVal := MinInt(segment.0, segment.1);
    if maxVal >= minVal then (maxVal - minVal + 1) as nat else 1
}

// <vc-helpers>
ghost predicate ValidInputFormat(s: string) {
    var lines := SplitLines(s);
    |lines| >= 1 &&
    exists n: nat, k: nat :: 
        ParsesAsIntegers(lines[0], n as int, k as int) && n > 0 && k > 0 && |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n && i < |lines| ==> 
            exists a: int, b: int :: ParsesAsIntegers(lines[i], a, b))
}

ghost predicate ParsedCorrectly(input: string, n: nat, k: nat, segments: seq<(int, int)>) {
    var lines := SplitLines(input);
    |lines| >= n + 1 && |segments| == n &&
    ParsesAsIntegers(lines[0], n as int, k as int) &&
    (forall i :: 0 <= i < n && i + 1 < |lines| ==> 
        ParsesAsIntegers(lines[i + 1], segments[i].0, segments[i].1))
}

predicate IsValidOutput(s: string) {
    |s| > 0 && s[|s| - 1] == '\n' && 
    (forall i :: 0 <= i < |s| - 1 ==> s[i] != '\n') &&
    IsNumericOutput(s[..|s| - 1])
}

function MinMovesToDivisible(segments: seq<(int, int)>, k: nat): nat
    requires k > 0
    ensures MinMovesToDivisible(segments, k) < k
{
    var totalCoverage := TotalCoverage(segments);
    var remainder := totalCoverage % k;
    if remainder == 0 then 0 else k - remainder
}

function TotalCoverage(segments: seq<(int, int)>): nat {
    if |segments| == 0 then 0
    else SegmentLength(segments[0]) + TotalCoverage(segments[1..])
}

function SegmentLength(segment: (int, int)): nat
    ensures SegmentLength(segment) >= 1
{
    var maxVal := MaxInt(segment.0, segment.1);
    var minVal := MinInt(segment.0, segment.1);
    if maxVal >= minVal then (maxVal - minVal + 1) as nat else 1
}

function SplitLines(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitLines(s)| ==> SplitLines(s)[i] as string == ""
{
    if s == "" then [""]
    else
        var idx := IndexOf(s, '\n');
        if idx < 0 then [s]
        else [s[..idx]] + SplitLines(s[idx+1..])
}

function IndexOf(s: string, c: char): int
    ensures IndexOf(s, c) < 0 || (0 <= IndexOf(s, c) < |s| && s[IndexOf(s, c)] == c)
    ensures IndexOf(s, c) == -1 <==> forall i :: 0 <= i < |s| ==> s[i] != c
{
    if |s| == 0 then -1
    else if s[0] == c then 0
    else
        var idx := IndexOf(s[1..], c);
        if idx < 0 then -1 else idx + 1
}

predicate ParsesAsIntegers(s: string, a: int, b: int)
{
    var parts := SplitBySpace(s);
    |parts| == 2 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) &&
    a == ParseInt(parts[0]) && b == ParseInt(parts[1])
}

function SplitBySpace(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitBySpace(s)| ==> SplitBySpace(s)[i] as string == ""
{
    if s == "" then [""]
    else
        var idx := IndexOf(s, ' ');
        if idx < 0 then [s]
        else [s[..idx]] + SplitBySpace(s[idx+1..])
}

predicate IsValidInteger(s: string) {
    |s| > 0 &&
    (if |s| == 1 then '0' <= s[0] <= '9'
     else
        var start := if s[0] == '-' then 1 else if s[0] == '+' then 1 else 0;
        (if start == 1 then |s| >= 2 else true) &&
        (forall i :: start <= i < |s| ==> '0' <= s[i] <= '9')
    )
}

function ParseInt(s: string): int
    requires IsValidInteger(s)
{
    if s[0] == '-' then -ParseNat(s[1..])
    else if s[0] == '+' then ParseNat(s[1..])
    else ParseNat(s)
}

function ParseNat(s: string): nat
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires |s| > 0
{
    if |s| == 1 then (s[0] - '0') as nat
    else 10 * ParseNat(s[..|s|-1]) + (s[|s|-1] - '0') as nat
}

predicate ContainsNewline(s: string)
{
    exists i :: 0 <= i < |s| && s[i] == '\n'
}

predicate IsNumericOutput(s: string)
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function IntToString(x: int): string
{
    if x < 0 then "-" + IntToString(-x)
    else if x < 10 then [ ('0' + x as char) ]
    else IntToString(x / 10) + IntToString(x % 10)
}

function MaxInt(a: int, b: int): int
{
    if a > b then a else b
}

function MinInt(a: int, b: int): int
{
    if a < b then a else b
}

lemma SplitLinesPreservesLength(s: string, n: nat)
    ensures |SplitLines(s)| == n ==> |s| >= n - 1
{
    if n == 0 {
        assert |s| >= -1;
    } else if n == 1 {
        assert IndexOf(s, '\n') < 0;
    } else {
        calc {
            |s| >= IndexOf(s, '\n') + 1 + |s[IndexOf(s, '\n')+1..]|;
            >= 0 + 1 + (n - 1 - 1);
            == n - 1;
        }
    }
}

lemma ParsedCorrectlyImpliesValidFormat(input: string, n: nat, k: nat, segments: seq<(int, int)>)
    requires ParsedCorrectly(input, n, k, segments)
    ensures ValidInputFormat(input)
{
    var lines := SplitLines(input);
    assert |lines| >= n + 1;
    assert n > 0 && k > 0;
    assert |lines| >= n + 1;
    assert ParsesAsIntegers(lines[0], n as int, k as int);
    forall i | 1 <= i <= n && i < |lines|
    {
        assert |segments| == n;
        assert i - 1 < |segments|;
        assert ParsesAsIntegers(lines[i], segments[i-1].0, segments[i-1].1);
    }
}

lemma {:autoinline} ValidInputFormatEnsuresParsedAsIntegers(s: string) returns (n: nat, k: nat)
    requires ValidInputFormat(s)
    ensures ParsesAsIntegers(SplitLines(s)[0], n as int, k as int)
    ensures n > 0 && k > 0
{
    var lines := SplitLines(s);
    reveal ValidInputFormat();
    assert exists n': nat, k': nat :: ParsesAsIntegers(lines[0], n' as int, k' as int) && n' > 0 && k' > 0;
    n, k := n', k';
}

lemma {:autoinline} ValidInputFormatEnsuresSegmentsParse(s: string, n: nat, k: nat) returns (segments: seq<(int, int)>)
    requires ValidInputFormat(s)
    ensures ParsedCorrectly(s, n, k, segments)
{
    var lines := SplitLines(s);
    reveal ValidInputFormat();
    assert parsesAsIntegers(lines[0], n as int, k as int);
    assert forall i | 1 <= i <= n && i < |lines| :: exists a: int, b: int :: ParsesAsIntegers(lines[i], a, b);
    segments := new (int, int)[n];
    for i := 0 to |segments|
        invariant forall j :: 0 <= j < i ==> 
            var a, b := segments[j]; 
            ParsesAsIntegers(lines[j+1], a, b)
    {
        if i < n {
            var a, b := 0, 0;
            calc {
                true;
                ==> {assert 1 <= i+1 <= n && i+1 < |lines|; }
                    exists a': int, b': int :: ParsesAsIntegers(lines[i+1], a', b');
                ==> {assert a', b' := 0, 0; }
                    ParsesAsIntegers(lines[i+1], a, b);
            }
            segments[i] := (a, b);
        }
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input| - 1] == '\n' || !ContainsNewline(stdin_input)
    ensures |result| == 0 || result[|result| - 1] == '\n'
    ensures ValidInputFormat(stdin_input) ==> 
        exists n: nat, k: nat, segments: seq<(int, int)> ::
            n > 0 && k > 0 && |segments| == n &&
            ParsedCorrectly(stdin_input, n, k, segments) &&
            result == IntToString(MinMovesToDivisible(segments, k)) + "\n"
    ensures ValidInputFormat(stdin_input) ==> IsValidOutput(result)
    ensures !ValidInputFormat(stdin_input) ==> 
        (result == "" || (|result| > 0 && result[|result| - 1] == '\n'))
// </vc-spec>
// <vc-code>
{
    if ValidInputFormat(stdin_input) {
        var n, k := ValidInputFormatEnsuresParsedAsIntegers(stdin_input);
        var segments := ValidInputFormatEnsuresSegmentsParse(stdin_input, n, k);
        var m := MinMovesToDivisible(segments, k);
        result := IntToString(m as int) + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

