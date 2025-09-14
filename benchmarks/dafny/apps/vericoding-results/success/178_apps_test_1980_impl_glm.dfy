predicate ValidInput(input: string)
{
    var lines := SplitLinesSpec(input);
    |lines| >= 1 && 
    |SplitWhitespaceSpec(lines[0])| >= 2 &&
    var n := ParseIntSpec(SplitWhitespaceSpec(lines[0])[0]);
    var k := ParseIntSpec(SplitWhitespaceSpec(lines[0])[1]);
    n > 0 && k > 0 && |lines| >= n + 1 &&
    (forall i :: 1 <= i <= n ==> 
        i < |lines| && |SplitWhitespaceSpec(lines[i])| >= 2)
}

function OptimalSegmentProfit(input: string, n: nat, k: int): int
    requires n > 0
    requires k > 0
    requires var lines := SplitLinesSpec(input);
        |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n ==> 
            i < |lines| && |SplitWhitespaceSpec(lines[i])| >= 2)
{
    var lines := SplitLinesSpec(input);
    var difficulties := seq(n, i requires 0 <= i < n => 
        ParseIntSpec(SplitWhitespaceSpec(lines[i + 1])[0]));
    var costs := seq(n, i requires 0 <= i < n => 
        ParseIntSpec(SplitWhitespaceSpec(lines[i + 1])[1]));

    MaxSubsegmentProfit(difficulties, costs, k)
}

function MaxSubsegmentProfit(difficulties: seq<int>, costs: seq<int>, k: int): int
    requires |difficulties| == |costs| >= 0
    requires k > 0
    requires forall i :: 0 <= i < |difficulties|-1 ==> difficulties[i] < difficulties[i+1]
{
    if |difficulties| == 0 then 0
    else
        var allSegmentProfits := seq(|difficulties|, l requires 0 <= l < |difficulties| => 
            seq(|difficulties| - l, len requires 0 <= len < |difficulties| - l =>
                SubsegmentProfit(difficulties, costs, k, l, l + len)));
        Max(0, MaxInNestedSeq(allSegmentProfits))
}

function SubsegmentProfit(difficulties: seq<int>, costs: seq<int>, k: int, l: nat, r: nat): int
    requires |difficulties| == |costs|
    requires k > 0
    requires 0 <= l <= r < |difficulties|
    requires forall i :: 0 <= i < |difficulties|-1 ==> difficulties[i] < difficulties[i+1]
{
    var length := r - l + 1;
    var revenue := length * k;
    var costSum := SumRange(costs, l, r);
    var gap := if l == r then 0 else MaxGapSquared(difficulties, l, r);
    revenue - costSum - gap
}

function SplitLinesSpec(s: string): seq<string>
{
    []
}

function SplitWhitespaceSpec(s: string): seq<string>
{
    []
}

function ParseIntSpec(s: string): int
{
    0
}

function IntToStringResult(n: int): string
{
    "0"
}

// <vc-helpers>
function SumRange(s: seq<int>, l: int, r: int): int
    requires 0 <= l <= r < |s|
    decreases r - l
{
    if l == r then s[l] else s[l] + SumRange(s, l + 1, r)
}

function MaxGapSquared(a: seq<int>, l: int, r: int): int
    requires 0 <= l <= r < |a|
    requires forall i :: 0 <= i < |a|-1 ==> a[i] < a[i+1]
    decreases r - l
{
    if r - l < 1 then 0
    else (a[r] - a[l]) * (a[r] - a[l])
}

function TotalElements(s: seq<seq<int>>): nat
    requires forall i :: 0 <= i < |s| ==> |s[i]| > 0
    decreases |s|
{
    if |s| == 0 then 0 else |s[0]| + TotalElements(s[1..])
}

function MaxInNestedSeq(s: seq<seq<int>>): int
    requires |s| > 0 && (forall i :: 0 <= i < |s| ==> |s[i]| > 0)
    ensures forall i :: 0 <= i < |s| ==> forall j :: 0 <= j < |s[i]| ==> MaxInNestedSeq(s) >= s[i][j]
    ensures exists i :: 0 <= i < |s| && exists j :: 0 <= j < |s[i]| && MaxInNestedSeq(s) == s[i][j]
    decreases TotalElements(s)
{
    if |s| == 1 then MaxInSeq(s[0])
    else
        var maxRest := MaxInNestedSeq(s[1..]);
        var maxFirst := MaxInSeq(s[0]);
        if maxFirst >= maxRest then maxFirst else maxRest
}

function MaxInSeq(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> MaxInSeq(s) >= s[i]
    ensures exists i :: 0 <= i < |s| && MaxInSeq(s) == s[i]
    decreases |s|
{
    if |s| == 1 then s[0]
    else
        var maxTail := MaxInSeq(s[1..]);
        if s[0] >= maxTail then s[0] else maxTail
}

function Max(a: int, b: int): int
{
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var lines := SplitLinesSpec(input);
        (|lines| == 0 || |lines| == 1 || 
         |SplitWhitespaceSpec(lines[0])| < 2 ||
         ParseIntSpec(SplitWhitespaceSpec(lines[0])[0]) <= 0) ==> 
        result == "0\n"
    ensures ValidInput(input) ==>
        (var lines := SplitLinesSpec(input);
         var n := ParseIntSpec(SplitWhitespaceSpec(lines[0])[0]);
         var k := ParseIntSpec(SplitWhitespaceSpec(lines[0])[1]);
         exists profit: int :: 
            profit >= 0 && 
            result == IntToStringResult(profit) + "\n" &&
            profit == OptimalSegmentProfit(input, n, k))
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        return "0\n";
    }

    var lines := SplitLinesSpec(input);
    var first_line_parts := SplitWhitespaceSpec(lines[0]);
    var n := ParseIntSpec(first_line_parts[0]);
    var k := ParseIntSpec(first_line_parts[1]);
    
    assert |lines| >= n + 1;
    assert 1 <= n <= |lines| - 1;
    assert forall i :: 1 <= i <= n ==> i < |lines| && |SplitWhitespaceSpec(lines[i])| >= 2;

    var difficulties := seq(n, i requires 0 <= i < n => 
        ParseIntSpec(SplitWhitespaceSpec(lines[i + 1])[0]));
    var costs := seq(n, i requires 0 <= i < n => 
        ParseIntSpec(SplitWhitespaceSpec(lines[i + 1])[1]));
    
    assert |difficulties| == |costs| == n;

    var profit := OptimalSegmentProfit(input, n, k);
    return IntToStringResult(profit) + "\n";
}
// </vc-code>

