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
// </vc-helpers>

// <vc-spec>
method solve(n: int, c: int, prices: seq<int>) returns (result: int)
    requires ValidInput(n, c, prices)
    ensures CorrectResult(n, c, prices, result)
// </vc-spec>
// <vc-code>
{
    var maxProfitSoFar := 0;
    var currentProfit := 0;

    // The loop iterates from the second to the last day.
    // The prices array has 'n' elements, indexed from 0 to n-1.
    // We are interested in profits from buying on day i and selling on day i+1.
    // So, we iterate from i = 0 to n-2.
    // 'day' in ProfitForDay corresponds to 'i' in this loop.
    // We need to compare prices[i] and prices[i+1].
    // So the loop goes from i = 0 to n-2.
    // Because prices[j] and prices[j+1] are used, the effective end of iteration is n-2.
    // Loop invariant:
    // 0 <= i <= n - 1
    // maxProfitSoFar is the maximum difference (prices[k] - prices[k+1] - c) for 0 <= k < i
    // or 0 if all such differences are negative.
    // maxProfitSoFar >= 0 && currentProfit >= 0

    for i := 0 to n - 2
        invariant 0 <= i <= n - 1
        invariant maxProfitSoFar >= 0
        invariant forall k :: 0 <= k < i ==> ProfitForDay(prices, k, c) <= maxProfitSoFar || maxProfitSoFar == 0
        invariant (exists k :: 0 <= k < i && ProfitForDay(prices, k, c) == maxProfitSoFar) ||
                  (forall k :: 0 <= k < i && ProfitForDay(prices, k, c) < 0 && maxProfitSoFar == 0) ||
                  (i == 0 && maxProfitSoFar == 0) // Case for initial state of i
    {
        var profitForThisDay := ProfitForDay(prices, i, c);
        // We want to accumulate positive profits. If adding the current profit makes it negative, reset to 0.
        // This effectively finds the maximum subarray sum where elements are
        // ProfitForDay(prices, i, c). This is Kadane's algorithm variant.
        currentProfit := currentProfit + profitForThisDay;
        if currentProfit < 0 {
            currentProfit := 0;
        }
        maxProfitSoFar := Max(maxProfitSoFar, currentProfit);
    }
    result := maxProfitSoFar;
}
// </vc-code>

