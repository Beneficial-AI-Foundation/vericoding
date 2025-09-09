/*
Find maximum profit from borrowing a honey barrel on day d, selling it for price x_d,
buying a new barrel on day d+1 for price x_{d+1}, and paying rental cost c.
Profit = x_d - x_{d+1} - c. Only execute if profitable, otherwise return 0.
*/

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
// </vc-helpers>

// <vc-spec>
method solve(n: int, c: int, prices: seq<int>) returns (result: int)
    requires ValidInput(n, c, prices)
    ensures CorrectResult(n, c, prices, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
