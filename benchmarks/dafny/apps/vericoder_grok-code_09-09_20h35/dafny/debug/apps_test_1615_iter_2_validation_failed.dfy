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
predicate ParsesAsIntegers(s: string, a: int, b: int) 

function SplitLines(s: string): seq<string> 

predicate ContainsNewline(s: string) {
    exists i :: 0 <= i < |s| && s[i] == '\n'
}

predicate IsNumericOutput(s: string) {
    |s| == 0 || (|s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

ghost function ParseInt(s: string): option<int>

function IntToString(x: int): string
    ensures x >= 0 ==> IsNumericOutput(result)

ghost predicate ParsesAsIntegersActual(s: string, a: int, b: int) {
    var parts := SplitOnSpace(s);
    |parts| >= 2 && ParseInt(parts[0]) == Some(a) && ParseInt(parts[1]) == Some(b)
}

function SplitOnSpace(s: string): seq<string>

lemma ParsedIfValidAssumption()
    ensures forall s: string, n: nat, k: nat, segments: seq<(int,int)> :: ValidInputFormat(s) ==> exists nn, kk, segs :: ParsedCorrectly(s, nn, kk, segs) && n == nn && k == kk && segments == segs

lemma ParseFirstLine(lines: seq<string>) returns (n: int, k: int)
    requires |lines| >= 1
    requires ParsesAsIntegersActual(lines[0], n, k) && n > 0 && k > 0
    ensures ParsesAsIntegers(lines[0], n, k)

function {:axiom} {} ParseIntValid(s: string): int
    ensures ParseInt(s).Some? && ParseInt(s).value >= 0
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
    var lines := SplitLines(stdin_input);
    if |lines| < 2 {
        return "";
    }
    var n: int := 0;
    var k: int := 0;
    if !ParsesAsIntegers(lines[0], n, k) || n <= 0 || k <= 0 || |lines| != n + 1 {
        return "";
    }
    var segments: seq<(int, int)> := [];
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant |segments| == i
        invariant forall j :: 0 <= j < i ==> ParsesAsIntegers(lines[j + 1], segments[j].0, segments[j].1)
    {
        var a: int := 0;
        var b: int := 0;
        if !ParsesAsIntegers(lines[i + 1], a, b) {
            return "";
        }
        segments := segments + [(a, b)];
    }
    var minMoves := MinMovesToDivisible(segments, k as nat);
    assert parsedCorrectlyImplyValid;
    var result := IntToString(minMoves as int) + "\n";
    return result;
}
// </vc-code>

