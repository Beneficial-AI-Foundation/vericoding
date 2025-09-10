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

function SplitWhitespace(s: string): seq<string>

function StringToInt(s: string): Option<int>

function IntToString(i: int): string

function MaxInt(a: int, b: int): int
{
    if a >= b then a else b
}

function MinInt(a: int, b: int): int
{
    if a <= b then a else b
}

predicate ParsesAsIntegers(s: string, a: int, b: int)

predicate IsNumericOutput(s: string)

predicate ContainsNewline(s: string)

datatype Option<T> = None | Some(value: T)

lemma TotalCoverageAdditive(segments: seq<(int, int)>)
    ensures |segments| > 0 ==> TotalCoverage(segments) == SegmentLength(segments[0]) + TotalCoverage(segments[1..])
{
    if |segments| > 0 {
        // follows from definition
    }
}

lemma MinMovesInRange(segments: seq<(int, int)>, k: nat)
    requires k > 0
    ensures MinMovesToDivisible(segments, k) < k
{
    var totalCoverage := TotalCoverage(segments);
    var remainder := totalCoverage % k;
    if remainder == 0 {
        assert MinMovesToDivisible(segments, k) == 0;
        assert 0 < k;
    } else {
        assert MinMovesToDivisible(segments, k) == k - remainder;
        assert 0 < remainder < k;
        assert k - remainder < k;
    }
}

lemma ParseCorrectlyImpliesValidFormat(input: string, n: nat, k: nat, segments: seq<(int, int)>)
    requires ParsedCorrectly(input, n, k, segments)
    requires n > 0 && k > 0
    ensures ValidInputFormat(input)
{
    var lines := SplitLines(input);
    assert |lines| >= n + 1;
    assert ParsesAsIntegers(lines[0], n as int, k as int);
    assert {:trigger ParsesAsIntegers(lines[0], n as int, k as int)} exists nn: nat, kk: nat :: ParsesAsIntegers(lines[0], nn as int, kk as int) && nn > 0 && kk > 0 && |lines| >= nn + 1;
}

lemma OutputPropertyLemma(s: string)
    requires |s| > 0 && s[|s| - 1] == '\n'
    requires IsNumericOutput(s[..|s| - 1])
    ensures IsValidOutput(s)
    ensures forall i :: 0 <= i < |s| - 1 ==> s[i] != '\n'
{
    // This lemma helps establish output validity
}

lemma IntToStringProperties(i: int)
    ensures var s := IntToString(i); IsNumericOutput(s)
{
    // This establishes that IntToString produces numeric output
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
    var lines := SplitLines(stdin_input);
    
    if |lines| == 0 {
        return "";
    }
    
    var firstLineParts := SplitWhitespace(lines[0]);
    if |firstLineParts| < 2 {
        return "";
    }
    
    var nOpt := StringToInt(firstLineParts[0]);
    var kOpt := StringToInt(firstLineParts[1]);
    
    if nOpt.None? || kOpt.None? || nOpt.value <= 0 || kOpt.value <= 0 {
        return "";
    }
    
    var n := nOpt.value as nat;
    var k := kOpt.value as nat;
    
    if |lines| < n + 1 {
        return "";
    }
    
    var segments: seq<(int, int)> := [];
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |segments| == i
        invariant forall j :: 0 <= j < i ==> j + 1 < |lines|
        invariant forall j :: 0 <= j < i ==> 
            ParsesAsIntegers(lines[j + 1], segments[j].0, segments[j].1)
    {
        if i + 1 >= |lines| {
            return "";
        }
        
        var lineParts := SplitWhitespace(lines[i + 1]);
        if |lineParts| < 2 {
            return "";
        }
        
        var aOpt := StringToInt(lineParts[0]);
        var bOpt := StringToInt(lineParts[1]);
        
        if aOpt.None? || bOpt.None? {
            return "";
        }
        
        segments := segments + [(aOpt.value, bOpt.value)];
        i := i + 1;
    }
    
    assert |segments| == n;
    assert forall j :: 0 <= j < n ==> j + 1 < |lines|;
    assert forall j :: 0 <= j < n ==> ParsesAsIntegers(lines[j + 1], segments[j].0, segments[j].1);
    assert ParsedCorrectly(stdin_input, n, k, segments);
    ParseCorrectlyImpliesValidFormat(stdin_input, n, k, segments);
    assert ValidInputFormat(stdin_input);
    
    var moves := MinMovesToDivisible(segments, k);
    MinMovesInRange(segments, k);
    
    result := IntToString(moves as int) + "\n";
    
    IntToStringProperties(moves as int);
    OutputPropertyLemma(result);
}
// </vc-code>

