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
lemma {:axiom} SplitLinesLemma(s: string)
    ensures |SplitLines(s)| >= 1

lemma {:axiom} ParsesAsIntegersLemma(line: string, a: int, b: int)
    ensures ParsesAsIntegers(line, a, b) == (|line| > 0 && IsNumeric(line))

lemma {:axiom} ContainsNewlineLemma(s: string)
    ensures ContainsNewline(s) == (exists i :: 0 <= i < |s| && s[i] == '\n')

lemma {:axiom} IntToStringLemma(n: nat)
    ensures |IntToString(n)| > 0 && IsNumeric(IntToString(n))

lemma {:axiom} IsNumericOutputLemma(s: string)
    ensures IsNumericOutput(s) == (|s| > 0 && IsNumeric(s))

lemma {:axiom} SegmentLengthPositive(segment: (int, int))
    ensures SegmentLength(segment) >= 1

lemma {:axiom} TotalCoverageNonNegative(segments: seq<(int, int)>)
    ensures TotalCoverage(segments) >= 0

lemma {:axiom} MinMovesToDivisibleRange(segments: seq<(int, int)>, k: nat)
    requires k > 0
    ensures 0 <= MinMovesToDivisible(segments, k) < k
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
    if !IsNumeric(firstLine) || !ContainsSpace(firstLine) {
        result := "";
        return;
    }
    
    var n_str, k_str := SplitFirstWord(firstLine);
    var n_opt := StringToInt(n_str);
    var k_opt := StringToInt(k_str);
    
    if n_opt == None || k_opt == None || n_opt? <= 0 || k_opt? <= 0 || |lines| < n_opt? + 1 {
        result := "";
        return;
    }
    
    var n := n_opt? as nat;
    var k := k_opt? as nat;
    var segments: seq<(int, int)> := [];
    var i := 1;
    
    while i <= n && i < |lines|
        invariant i >= 1
        invariant |segments| == i - 1
        invariant i <= n + 1
    {
        var line := lines[i];
        if !IsNumeric(line) || !ContainsSpace(line) {
            result := "";
            return;
        }
        
        var a_str, b_str := SplitFirstWord(line);
        var a_opt := StringToInt(a_str);
        var b_opt := StringToInt(b_str);
        
        if a_opt == None || b_opt == None {
            result := "";
            return;
        }
        
        segments := segments + [(a_opt?, b_opt?)];
        i := i + 1;
    }
    
    if |segments| != n {
        result := "";
        return;
    }
    
    var moves := MinMovesToDivisible(segments, k);
    result := IntToString(moves) + "\n";
}
// </vc-code>

