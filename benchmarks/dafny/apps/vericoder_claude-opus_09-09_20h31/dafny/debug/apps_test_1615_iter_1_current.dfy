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
lemma MinMovesLessThanK(segments: seq<(int, int)>, k: nat)
    requires k > 0
    ensures MinMovesToDivisible(segments, k) < k
{
    var totalCoverage := TotalCoverage(segments);
    var remainder := totalCoverage % k;
    if remainder == 0 {
        assert MinMovesToDivisible(segments, k) == 0;
        assert 0 < k;
    } else {
        assert 0 < remainder < k;
        assert MinMovesToDivisible(segments, k) == k - remainder;
        assert k - remainder < k;
    }
}

lemma ParsedCorrectlyImpliesValidFormat(input: string, n: nat, k: nat, segments: seq<(int, int)>)
    requires ParsedCorrectly(input, n, k, segments)
    ensures ValidInputFormat(input)
{
    var lines := SplitLines(input);
    assert |lines| >= n + 1;
    assert ParsesAsIntegers(lines[0], n as int, k as int);
    assert n > 0 && k > 0;
    assert forall i :: 1 <= i <= n && i < |lines| ==> 
        exists a: int, b: int :: ParsesAsIntegers(lines[i], a, b);
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
    
    var n, k := ParseTwoIntegers(lines[0]);
    
    if n <= 0 || k <= 0 || |lines| < n + 1 {
        return "";
    }
    
    var segments: seq<(int, int)> := [];
    var i := 1;
    
    while i <= n && i < |lines|
        invariant 1 <= i <= n + 1
        invariant i <= |lines|
        invariant |segments| == i - 1
        invariant forall j :: 0 <= j < |segments| ==> 
            ParsesAsIntegers(lines[j + 1], segments[j].0, segments[j].1)
    {
        var a, b := ParseTwoIntegers(lines[i]);
        segments := segments + [(a, b)];
        i := i + 1;
    }
    
    if |segments| != n {
        return "";
    }
    
    assert ParsedCorrectly(stdin_input, n, k, segments);
    
    var moves := MinMovesToDivisible(segments, k);
    MinMovesLessThanK(segments, k);
    
    result := IntToString(moves) + "\n";
    
    assert IsValidOutput(result) by {
        assert |result| > 0;
        assert result[|result| - 1] == '\n';
        var s_without_newline := result[..|result| - 1];
        assert s_without_newline == IntToString(moves);
        assert IsNumericOutput(s_without_newline);
        assert forall i :: 0 <= i < |result| - 1 ==> result[i] != '\n';
    }
}
// </vc-code>

