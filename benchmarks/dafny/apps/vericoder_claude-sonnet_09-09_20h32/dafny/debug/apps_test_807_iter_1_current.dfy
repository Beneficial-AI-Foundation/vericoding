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
lemma ProfitBoundsLemma(prices: seq<int>, c: int, i: int, maxProfit: int)
    requires ValidInput(|prices|, c, prices)
    requires 0 <= i < |prices| - 1
    requires maxProfit >= ProfitForDay(prices, i, c)
    requires (forall j :: 0 <= j < |prices| - 1 ==> ProfitForDay(prices, j, c) <= maxProfit)
    ensures maxProfit >= ProfitForDay(prices, i, c)
{
}

lemma MaxProfitExistsLemma(prices: seq<int>, c: int, maxProfit: int)
    requires ValidInput(|prices|, c, prices)
    requires maxProfit > 0
    requires (forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= maxProfit)
    ensures exists i :: 0 <= i < |prices| - 1 && ProfitForDay(prices, i, c) == maxProfit
{
    var found := false;
    var idx := 0;
    while idx < |prices| - 1
        invariant 0 <= idx <= |prices| - 1
        invariant !found ==> (forall j :: 0 <= j < idx ==> ProfitForDay(prices, j, c) < maxProfit)
    {
        if ProfitForDay(prices, idx, c) == maxProfit {
            found := true;
            break;
        }
        idx := idx + 1;
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
    result := 0;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant result >= 0
        invariant forall j :: 0 <= j < i ==> ProfitForDay(prices, j, c) <= result
        invariant result == 0 ==> (forall j :: 0 <= j < i ==> ProfitForDay(prices, j, c) <= 0)
        invariant result > 0 ==> (exists j :: 0 <= j < i && ProfitForDay(prices, j, c) == result)
    {
        var profit := prices[i] - prices[i + 1] - c;
        
        if profit > result {
            result := profit;
        }
        
        i := i + 1;
    }
}
// </vc-code>

