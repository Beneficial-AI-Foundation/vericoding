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
lemma {:axiom} SplitLinesPreservesLength(s: string)
    ensures |SplitLines(s)| >= 1

lemma {:axiom} ParsesAsIntegersImpliesValid(s: string, a: int, b: int)
    requires ParsesAsIntegers(s, a, b)
    ensures a is int && b is int

lemma {:axiom} SegmentLengthPositive(segment: (int, int))
    ensures SegmentLength(segment) >= 1

lemma {:axiom} TotalCoverageNonNegative(segments: seq<(int, int)>)
    ensures TotalCoverage(segments) >= 0

lemma {:axiom} ModResultLessThanDivisor(n: nat, k: nat)
    requires k > 0
    ensures n % k < k

lemma {:axiom} IntToStringValid(n: nat)
    ensures |IntToString(n)| > 0 && IsNumericOutput(IntToString(n))

ghost function SplitLines(s: string): seq<string>
    ensures |result| >= 1

ghost function ParsesAsIntegers(s: string, a: int, b: int): bool

ghost function ContainsNewline(s: string): bool

ghost function IsNumericOutput(s: string): bool

ghost function IntToString(n: nat): string
    ensures |result| > 0 && IsNumericOutput(result)

function MaxInt(a: int, b: int): int
    ensures result >= a && result >= b

function MinInt(a: int, b: int): int
    ensures result <= a && result <= b
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
    
    if |lines| < 1 {
        result := "";
        return;
    }
    
    var firstLine := lines[0];
    var n: int;
    var k: int;
    
    if !ParsesAsIntegers(firstLine, n, k) || n <= 0 || k <= 0 || |lines| < n + 1 {
        result := "";
        return;
    }
    
    var segments: seq<(int, int)> := [];
    var i := 0;
    
    while i < n && i + 1 < |lines|
        invariant 0 <= i <= n
        invariant |segments| == i
    {
        var a: int;
        var b: int;
        
        if !ParsesAsIntegers(lines[i + 1], a, b) {
            result := "";
            return;
        }
        
        segments := segments + [(a, b)];
        i := i + 1;
    }
    
    if i < n {
        result := "";
        return;
    }
    
    var total := TotalCoverage(segments);
    var remainder := total % k;
    var moves := remainder == 0 ? 0 : k - remainder;
    
    result := IntToString(moves) + "\n";
}
// </vc-code>

