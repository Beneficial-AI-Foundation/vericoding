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
function Max(a: int, b: int): int { if a > b then a else b }

function MaxInNestedSeq(s: seq<seq<int>>): int
    requires (forall i :: 0 <= i < |s| ==> |s[i]| > 0)
    ensures (exists i, j :: 0 <= i < |s| && 0 <= j < |s[i]| && MaxInNestedSeq(s) == s[i][j])
    ensures (forall i, j :: 0 <= i < |s| && 0 <= j < |s[i]| ==> MaxInNestedSeq(s) >= s[i][j])
{
    if |s| == 0 then 0 // This case should be covered by requires, but for termination
    else
        var currentMax := s[0][0];
        for i := 0 to |s| - 1
            invariant 0 <= i <= |s|
            invariant (exists idx_i, idx_j :: 0 <= idx_i < i && 0 <= idx_j < |s[idx_i]| && currentMax == s[idx_i][idx_j]) || (i == 0 && currentMax == s[0][0])
            invariant (forall idx_i, idx_j :: 0 <= idx_i < i && 0 <= idx_j < |s[idx_i]| ==> currentMax >= s[idx_i][idx_j])
            invariant (i > 0 ==> forall idx_j :: 0 <= idx_j < |s[i-1]| ==> currentMax >= s[i-1][idx_j])
        {
            if |s[i]| > 0 {
                for j := 0 to |s[i]| - 1
                    invariant 0 <= j <= |s[i]|
                    invariant (exists idx_i, idx_j :: 0 <= idx_i < i && 0 <= idx_j < |s[idx_i]| && currentMax == s[idx_i][idx_j]) || (i == 0 && currentMax == s[0][0]) || (exists idx_j_prev :: 0 <= idx_j_prev < j && currentMax == s[i][idx_j_prev])
                    invariant (forall idx_i_inner :: 0 <= idx_i_inner < i ==> forall idx_j_inner :: 0 <= idx_j_inner < |s[idx_i_inner]| ==> currentMax >= s[idx_i_inner][idx_j_inner])
                    invariant (forall idx_j_inner :: 0 <= idx_j_inner < j ==> currentMax >= s[i][idx_j_inner])
                {
                    currentMax := Max(currentMax, s[i][j]);
                }
            }
        }
        currentMax
}

function SumRange(a: seq<int>, l: nat, r: nat): int
    requires 0 <= l <= r < |a|
{
    if l == r then a[l]
    else a[l] + SumRange(a, l + 1, r)
}

function MaxGap(a: seq<int>, l: nat, r: nat): int
    requires 0 <= l <= r < |a|
    requires forall i :: 0 <= i < |a|-1 ==> a[i] < a[i+1]
    ensures MaxGap(a, l, r) >= 0
{
    if l == r then 0
    else if l + 1 == r then a[r] - a[l]
    else Max(a[l+1] - a[l], MaxGap(a, l + 1, r))
}

function MaxGapSquared(a: seq<int>, l: nat, r: nat): int
    requires 0 <= l <= r < |a|
    requires forall i :: 0 <= i < |a|-1 ==> a[i] < a[i+1]
    ensures MaxGapSquared(a, l, r) >= 0
{
    var mg := MaxGap(a, l, r);
    mg * mg
}

predicate method isValidInputSplit(lines: seq<string>)
{
    |lines| >= 1 &&
    |SplitWhitespaceSpec(lines[0])| >= 2
}

predicate method isValidInputN(n_str: string)
{
    var n := ParseIntSpec(n_str);
    n > 0
}

predicate method isValidInputK(k_str: string)
{
    var k := ParseIntSpec(k_str);
    k > 0
}

predicate method isValidInputLinesNandK(lines: seq<string>, n: int, k: int)
{
    |lines| >= n + 1 &&
    (forall i :: 1 <= i <= n ==>
        i < |lines| && |SplitWhitespaceSpec(lines[i])| >= 2)
}

function method GetNAndK(lines: seq<string>) returns (n: int, k: int)
    requires isValidInputSplit(lines)
    requires isValidInputN(SplitWhitespaceSpec(lines[0])[0])
    requires isValidInputK(SplitWhitespaceSpec(lines[0])[1])
    ensures n == ParseIntSpec(SplitWhitespaceSpec(lines[0])[0])
    ensures k == ParseIntSpec(SplitWhitespaceSpec(lines[0])[1])
{
    (ParseIntSpec(SplitWhitespaceSpec(lines[0])[0]), ParseIntSpec(SplitWhitespaceSpec(lines[0])[1]))
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
    if !isValidInputSplit(lines) ||
       !isValidInputN(SplitWhitespaceSpec(lines[0])[0]) ||
       !isValidInputK(SplitWhitespaceSpec(lines[0])[1])
    {
        return "0\n";
    }

    var n_str := SplitWhitespaceSpec(lines[0])[0];
    var k_str := SplitWhitespaceSpec(lines[0])[1];

    var n := ParseIntSpec(n_str);
    var k := ParseIntSpec(k_str);

    if n <= 0 || k <= 0 || !isValidInputLinesNandK(lines, n, k)
    {
        return "0\n";
    }

    var profit := OptimalSegmentProfit(input, n, k);
    return IntToStringResult(profit) + "\n";
}
// </vc-code>

