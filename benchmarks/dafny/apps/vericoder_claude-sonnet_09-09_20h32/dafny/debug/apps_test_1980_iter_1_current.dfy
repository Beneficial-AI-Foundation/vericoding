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
function Max(a: int, b: int): int
{
    if a >= b then a else b
}

function MaxInNestedSeq(seqs: seq<seq<int>>): int
    requires |seqs| > 0
    requires forall i :: 0 <= i < |seqs| ==> |seqs[i]| > 0
{
    var maxValues := seq(|seqs|, i requires 0 <= i < |seqs| => MaxInSeq(seqs[i]));
    MaxInSeq(maxValues)
}

function MaxInSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else Max(s[0], MaxInSeq(s[1..]))
}

function SumRange(costs: seq<int>, l: nat, r: nat): int
    requires 0 <= l <= r < |costs|
{
    if l == r then costs[l]
    else costs[l] + SumRange(costs, l + 1, r)
}

function MaxGapSquared(difficulties: seq<int>, l: nat, r: nat): int
    requires 0 <= l < r < |difficulties|
    requires forall i :: 0 <= i < |difficulties|-1 ==> difficulties[i] < difficulties[i+1]
{
    var gaps := seq(r - l, i requires 0 <= i < r - l => 
        var gap := difficulties[l + i + 1] - difficulties[l + i];
        gap * gap);
    if |gaps| == 0 then 0 else MaxInSeq(gaps)
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
    var lines := SplitLinesSpec(input);
    
    if |lines| == 0 || |lines| == 1 {
        return "0\n";
    }
    
    var firstLineTokens := SplitWhitespaceSpec(lines[0]);
    if |firstLineTokens| < 2 {
        return "0\n";
    }
    
    var n := ParseIntSpec(firstLineTokens[0]);
    var k := ParseIntSpec(firstLineTokens[1]);
    
    if n <= 0 || k <= 0 {
        return "0\n";
    }
    
    if |lines| < n + 1 {
        return "0\n";
    }
    
    var validLines := true;
    var i := 1;
    while i <= n && validLines
        invariant 1 <= i <= n + 1
        invariant validLines ==> (forall j :: 1 <= j < i ==> 
            j < |lines| && |SplitWhitespaceSpec(lines[j])| >= 2)
    {
        if i >= |lines| || |SplitWhitespaceSpec(lines[i])| < 2 {
            validLines := false;
        }
        i := i + 1;
    }
    
    if !validLines {
        return "0\n";
    }
    
    var profit := OptimalSegmentProfit(input, n, k);
    return IntToStringResult(profit) + "\n";
}
// </vc-code>

