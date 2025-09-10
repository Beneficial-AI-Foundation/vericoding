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
    MaxProfitExistsHelper(prices, c, maxProfit, 0);
}

lemma MaxProfitExistsHelper(prices: seq<int>, c: int, maxProfit: int, start: int)
    requires ValidInput(|prices|, c, prices)
    requires maxProfit > 0
    requires 0 <= start < |prices| - 1
    requires (forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= maxProfit)
    requires exists i :: start <= i < |prices| - 1 && ProfitForDay(prices, i, c) == maxProfit
    ensures exists i :: 0 <= i < |prices| - 1 && ProfitForDay(prices, i, c) == maxProfit
    decreases |prices| - 1 - start
{
    if ProfitForDay(prices, start, c) == maxProfit {
        // Found it at start
    } else {
        assert exists i :: start + 1 <= i < |prices| - 1 && ProfitForDay(prices, i, c) == maxProfit;
        if start + 1 < |prices| - 1 {
            MaxProfitExistsHelper(prices, c, maxProfit, start + 1);
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
    result := 0;
    var i := 0;
    var maxIndex := -1;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant result >= 0
        invariant forall j :: 0 <= j < i ==> ProfitForDay(prices, j, c) <= result
        invariant result == 0 ==> (forall j :: 0 <= j < i ==> ProfitForDay(prices, j, c) <= 0)
        invariant result > 0 ==> (-1 <= maxIndex < i && maxIndex >= 0 && ProfitForDay(prices, maxIndex, c) == result)
        invariant result > 0 ==> (exists j :: 0 <= j < i && ProfitForDay(prices, j, c) == result)
    {
        var profit := prices[i] - prices[i + 1] - c;
        
        if profit > result {
            result := profit;
            maxIndex := i;
        }
        
        i := i + 1;
    }
    
    if result > 0 {
        assert maxIndex >= 0 && maxIndex < n - 1;
        assert ProfitForDay(prices, maxIndex, c) == result;
        assert exists j :: 0 <= j < n - 1 && ProfitForDay(prices, j, c) == result;
        assert forall k :: 0 <= k < n - 1 ==> ProfitForDay(prices, k, c) <= result;
        assert exists k :: maxIndex <= k < n - 1 && ProfitForDay(prices, k, c) == result;
        MaxProfitExistsHelper(prices, c, result, maxIndex);
    }
}
// </vc-code>

