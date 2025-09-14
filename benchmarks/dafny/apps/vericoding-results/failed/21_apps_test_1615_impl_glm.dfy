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
function SplitLines(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitLines(s)| ==> SplitLines(s)[i][|SplitLines(s)[i]| - 1] != '\n'
    ensures s == ConcatLines(SplitLines(s))
{
    if s == "" then []
    else var i := FindChar(s, '\n');
        if i < 0 then [s] else [s[..i]] + SplitLines(s[i+1..])
}
function FindChar(s: string, c: char): int
    ensures 0 <= FindChar(s, c) ==> s[FindChar(s, c)] == c && (forall j :: 0 <= j < FindChar(s, c) ==> s[j] != c)
    ensures FindChar(s, c) < 0 ==> (forall j :: 0 <= j < |s| ==> s[j] != c)
{
    if s == "" then -1
    else if s[0] == c then 0
    else var i := FindChar(s[1..], c); if i < 0 then -1 else i + 1
}
function ConcatLines(lines: seq<string>): string
    ensures |ConcatLines(lines)| == (if |lines| == 0 then 0 else (|lines| - 1) + |lines[|lines|-1]|)
    ensures forall i :: 0 <= i < |ConcatLines(lines)| && ConcatLines(lines)[i] == '\n' ==> 
        exists j :: 0 <= j < |lines| && i == LineStartIndex(lines, j) + |lines[j]|
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0]
    else lines[0] + "\n" + ConcatLines(lines[1..])
}
function LineStartIndex(lines: seq<string>, i: nat): nat
    requires 0 <= i < |lines|
    ensures LineStartIndex(lines, i) == (if i == 0 then 0 else LineStartIndex(lines, i-1) + |lines[i-1]| + 1)
{
    if i == 0 then 0 else LineStartIndex(lines, i-1) + |lines[i-1]| + 1
}
predicate ContainsNewline(s: string) {
    exists i :: 0 <= i < |s| && s[i] == '\n'
}
predicate ParsesAsIntegers(s: string, a: int, b: int) {
    s == IntToString(a) + " " + IntToString(b)
}
function IntToString(i: int): string {
    if i < 0 then "-" + IntToString(-i) else 
    if i == 0 then "0" else 
    if i < 10 then "0123456789"[i:i+1] else IntToString(i / 10) + "0123456789"[i % 10:i % 10 + 1]
}
predicate IsNumericOutput(s: string) {
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}
ghost method ParseFirstLine(s: string) returns (n: int, k: int)
    requires ParsesAsIntegers(s, n, k)
    ensures ParsesAsIntegers(s, n, k)
{
}
ghost method ParseLine(s: string) returns (a: int, b: int)
    requires ParsesAsIntegers(s, a, b)
    ensures ParsesAsIntegers(s, a, b)
{
}
method StringToInt(s: string) returns (i: int)
    requires IsNumericOutput(s) || s == "0" || (s[0] == '-' && IsNumericOutput(s[1:]))
    decreases |s|
{
    if s == "" {
        i := 0;
    } else if s[0] == '-' {
        i := -StringToInt(s[1:]);
    } else {
        if |s| == 0 {
            i := 0;
        } else {
            var digit := s[0] - '0';
            var rest := StringToInt(s[1:]);
            i := digit + 10 * rest;
        }
    }
}
method ParseTwoIntegers(s: string) returns (a: int, b: int)
    requires ParsesAsIntegers(s, a, b)
    ensures ParsesAsIntegers(s, a, b)
{
    var spaceIndex := 0;
    while spaceIndex < |s| && s[spaceIndex] != ' '
        invariant 0 <= spaceIndex <= |s|
        invariant forall j :: 0 <= j < spaceIndex ==> s[j] != ' '
    {
        spaceIndex := spaceIndex + 1;
    }
    assert s[spaceIndex] == ' ';
    var aStr := s[..spaceIndex];
    var bStr := s[spaceIndex+1..];
    a := StringToInt(aStr);
    b := StringToInt(bStr);
}
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
        var lines := SplitLines(stdin_input);
        var n, k := ParseTwoIntegers(lines[0]);
        var segments := new (int, int)[n];
        var i := 0;
        while i < n
            invariant 0 <= i <= n
            invariant forall j :: 0 <= j < i ==> 
                exists a: int, b: int :: ParsesAsIntegers(lines[j + 1], a, b) && segments[j] == (a, b)
        {
            var a, b := ParseTwoIntegers(lines[i + 1]);
            segments[i] := (a, b);
            i := i + 1;
        }
        var totalCoverage := TotalCoverage(segments);
        var knat := k as nat;
        var remainder := totalCoverage % knat;
        var moves := if remainder == 0 then 0 else knat - remainder;
        result := IntToString(moves as int) + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

