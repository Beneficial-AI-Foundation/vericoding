predicate ValidInput(n: int, c: int, prices: seq<int>) {
    n >= 2 && |prices| == n && c >= 0 &&
    (forall i :: 0 <= i < |prices| ==> prices[i] >= 0)
}

function ProfitForDay(prices: seq<int>, day: int, c: int): int
    requires 0 <= day < |prices| - 1
{
    prices[day] - prices[day + 1] - c
}

function MaxPossibleProfit(prices: seq<int>, c: int): int
    requires |prices| >= 2
{
    var profits := seq(|prices| - 1, i requires 0 <= i < |prices| - 1 => ProfitForDay(prices, i, c));
    if |profits| == 0 then 0 else
    var maxProfit := profits[0];
    if |profits| == 1 then maxProfit else
    seq_max(profits)
}

function seq_max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= seq_max(s[1..]) then s[0]
    else seq_max(s[1..])
}

predicate CorrectResult(n: int, c: int, prices: seq<int>, result: int) {
    ValidInput(n, c, prices) ==>
    (result >= 0 &&
     (result == 0 <==> (forall i :: 0 <= i < n - 1 ==> ProfitForDay(prices, i, c) <= 0)) &&
     (result > 0 ==> (exists i :: 0 <= i < n - 1 && ProfitForDay(prices, i, c) == result)) &&
     (forall i :: 0 <= i < n - 1 ==> ProfitForDay(prices, i, c) <= result))
}

// <vc-helpers>
function Max(a: int, b: int): int {
    if a > b then a else b
}

lemma lemma_seq_max_lower_bound(s: seq<int>)
    requires |s| > 0
    ensures forall x :: x in s ==> x <= seq_max(s)
{
    if |s| > 1 {
        if s[0] >= seq_max(s[1..]) {
            assert s[0] == seq_max(s);
            forall x | x in s[1..] ensures x <= seq_max(s[1..]) {
            }
        } else {
            assert seq_max(s[1..]) == seq_max(s);
            forall x | x in s[1..] ensures x <= seq_max(s[1..]) {
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, c: int, prices: seq<int>) returns (result: int)
    requires ValidInput(n, c, prices)
    ensures CorrectResult(n, c, prices, result)
// </vc-spec>
// <vc-code>
{
    var maxProfitSoFar := 0;
    var currentSegmentMaxProfit := 0;

    for i := 0 to n - 2
        invariant 0 <= i <= n - 1
        invariant maxProfitSoFar >= 0
        invariant currentSegmentMaxProfit >= 0
        invariant (forall k :: 0 <= k < i ==> ProfitForDay(prices, k, c) <= maxProfitSoFar) ||
                  (i == 0 && maxProfitSoFar == 0)
        invariant (exists k :: 0 <= k < i && ProfitForDay(prices, k, c) == maxProfitSoFar) ||
                  (forall k :: 0 <= k < i && ProfitForDay(prices, k, c) <= 0) ||
                  (i == 0 && maxProfitSoFar == 0)
        // This invariant shows that currentSegmentMaxProfit is the maximum profit ending at i-1
        // (or 0 if all profits in the current segment are negative)
        invariant (forall k :: 0 <= k < i ==> currentSegmentMaxProfit >= 0)
        invariant (exists k, l :: 0 <= k <= l < i &&
                   (sum j  := k to l : ProfitForDay(prices, j, c)) == currentSegmentMaxProfit) ||
                  (i == 0 && currentSegmentMaxProfit == 0) ||
                  (forall k, l :: 0 <= k <= l < i ==> (sum j := k to l : ProfitForDay(prices, j, c)) <= 0) && currentSegmentMaxProfit == 0
    {
        var profitForThisDay := ProfitForDay(prices, i, c);
        
        currentSegmentMaxProfit := currentSegmentMaxProfit + profitForThisDay;
        
        if currentSegmentMaxProfit < 0 {
            currentSegmentMaxProfit := 0;
        }
        
        maxProfitSoFar := Max(maxProfitSoFar, currentSegmentMaxProfit);
    }
    result := maxProfitSoFar;
}
// </vc-code>

