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
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, c: int, prices: seq<int>) returns (result: int)
    requires ValidInput(n, c, prices)
    ensures CorrectResult(n, c, prices, result)
// </vc-spec>
// <vc-code>
{
  result := 0;
  ghost var real_max := 0;
  for i: int := 0 to n-2
    invariant 0 <= i <= n - 1
    invariant (forall k :: 0 <= k < i ==> ProfitForDay(prices, k, c) <= real_max)
    invariant real_max >= 0
    invariant (forall k :: 0 <= k < i ==> ProfitForDay(prices, k, c) <= result)
    invariant forall k :: 0 <= k < i ==> ProfitForDay(prices, k, c) <= real_max
  {
    var profit := ProfitForDay(prices, i, c);
    if profit > real_max {
      real_max := profit;
    }
    if profit > result {
      result := profit;
    }
  }
  result := if real_max > 0 then real_max else 0;
}
// </vc-code>

