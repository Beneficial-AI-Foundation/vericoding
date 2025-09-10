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
function SumRange(costs: seq<int>, l: nat, r: nat): int
    requires |costs| > 0
    requires 0 <= l <= r < |costs|
    decreases r - l
{
    if l == r then
        costs[l]
    else
        SumRange(costs, l, r - 1) + costs[r]
}

function MaxGapSquared(difficulties: seq<int>, l: nat, r: nat): int
    requires |difficulties| > 0
    requires 0 <= l <= r < |difficulties|
    requires forall i :: 0 <= i < |difficulties|-1 ==> difficulties[i] < difficulties[i+1]
    decreases r - l
{
    if l == r then
        0
    else if l + 1 == r then
        (difficulties[r] - difficulties[l]) * (difficulties[r] - difficulties[l])
    else
        var mid := l + (r - l) / 2;
        max(MaxGapSquared(difficulties, l, mid), MaxGapSquared(difficulties, mid, r))
}

function MaxInNestedSeq(seqs: seq<seq<int>>): int
    requires |seqs| > 0
    decreases |seqs|
{
    if |seqs| == 1 then
        MaxInSeq(seqs[0])
    else
        max(MaxInSeq(seqs[0]), MaxInNestedSeq(seqs[1..]))
}

function MaxInSeq(arr: seq<int>): int
    requires |arr| > 0
    decreases |arr|
{
    if |arr| == 1 then
        arr[0]
    else
        max(arr[0], MaxInSeq(arr[1..]))
}

function MaxInSubseq(arr: seq<int>, start: int, end: int): int
    requires 0 <= start < end <= |arr|
    decreases end - start
{
    if end - start == 1 then
        arr[start]
    else
        var mid := start + (end - start) / 2;
        max(MaxInSubseq(arr, start, mid), MaxInSubseq(arr, mid, end))
}

function Max(a: int, b: int): int
{
    if a > b then a else b
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
    
    if |lines| == 0 || |lines| == 1 || |SplitWhitespaceSpec(lines[0])| < 2 {
        result := "0\n";
        return;
    }
    
    var firstLineParts := SplitWhitespaceSpec(lines[0]);
    var n := ParseIntSpec(firstLineParts[0]);
    var k := ParseIntSpec(firstLineParts[1]);
    
    if n <= 0 || k <= 0 || |lines| < n + 1 {
        result := "0\n";
        return;
    }
    
    var difficulties := seq(n, i requires 0 <= i < n => 
        ParseIntSpec(SplitWhitespaceSpec(lines[i + 1])[0]));
    var costs := seq(n, i requires 0 <= i < n => 
        ParseIntSpec(SplitWhitespaceSpec(lines[i + 1])[1]));
    
    var maxProfit := 0;
    var l := 0;
    while l < n
        invariant 0 <= l <= n
    {
        var r := l;
        while r < n
            invariant l <= r <= n
        {
            var profit := SubsegmentProfit(difficulties, costs, k, l, r);
            if profit > maxProfit {
                maxProfit := profit;
            }
            r := r + 1;
        }
        l := l + 1;
    }
    
    result := IntToStringResult(maxProfit) + "\n";
}
// </vc-code>

