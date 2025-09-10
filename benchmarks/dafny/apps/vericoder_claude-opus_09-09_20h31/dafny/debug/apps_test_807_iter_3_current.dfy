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
lemma SeqMaxProperties(s: seq<int>)
    requires |s| > 0
    ensures seq_max(s) in s
    ensures forall i :: 0 <= i < |s| ==> s[i] <= seq_max(s)
{
    if |s| == 1 {
        // Base case
    } else {
        SeqMaxProperties(s[1..]);
        if s[0] >= seq_max(s[1..]) {
            // s[0] is the max
            assert seq_max(s) == s[0];
        } else {
            // max is in s[1..]
            assert seq_max(s) == seq_max(s[1..]);
            assert seq_max(s[1..]) in s[1..];
        }
    }
}

lemma MaxProfitCorrectness(prices: seq<int>, c: int, result: int)
    requires |prices| >= 2
    requires result == MaxPossibleProfit(prices, c)
    ensures result >= 0
    ensures result == 0 <==> (forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= 0)
    ensures result > 0 ==> (exists i :: 0 <= i < |prices| - 1 && ProfitForDay(prices, i, c) == result)
    ensures forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= result
{
    var profits := seq(|prices| - 1, i requires 0 <= i < |prices| - 1 => ProfitForDay(prices, i, c));
    
    if |profits| == 0 {
        assert |prices| - 1 == 0;
        assert false; // Can't happen since |prices| >= 2
    } else if |profits| == 1 {
        assert result == profits[0];
        assert profits[0] == ProfitForDay(prices, 0, c);
    } else {
        SeqMaxProperties(profits);
        assert result == seq_max(profits);
        assert result in profits;
        
        // Find the index where result occurs
        var idx :| 0 <= idx < |profits| && profits[idx] == result;
        assert profits[idx] == ProfitForDay(prices, idx, c);
        
        // All elements are <= result
        forall i | 0 <= i < |prices| - 1
            ensures ProfitForDay(prices, i, c) <= result
        {
            assert profits[i] == ProfitForDay(prices, i, c);
            assert profits[i] <= seq_max(profits);
        }
    }
    
    // Handle the zero case
    if result == 0 {
        if exists i :: 0 <= i < |prices| - 1 && ProfitForDay(prices, i, c) > 0 {
            var i :| 0 <= i < |prices| - 1 && ProfitForDay(prices, i, c) > 0;
            assert profits[i] == ProfitForDay(prices, i, c);
            assert profits[i] > 0;
            assert result >= profits[i];
            assert result > 0;
            assert false;
        }
    } else {
        assert result > 0;
        assert result in profits;
        var i :| 0 <= i < |profits| && profits[i] == result;
        assert profits[i] == ProfitForDay(prices, i, c);
        assert ProfitForDay(prices, i, c) == result;
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
    var maxProfit := 0;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant maxProfit >= 0
        invariant forall j :: 0 <= j < i ==> ProfitForDay(prices, j, c) <= maxProfit
        invariant maxProfit > 0 ==> exists j :: 0 <= j < i && ProfitForDay(prices, j, c) == maxProfit
        invariant maxProfit == 0 ==> forall j :: 0 <= j < i ==> ProfitForDay(prices, j, c) <= 0
    {
        var profit := prices[i] - prices[i + 1] - c;
        assert profit == ProfitForDay(prices, i, c);
        
        if profit > maxProfit {
            maxProfit := profit;
        }
        
        i := i + 1;
    }
    
    result := maxProfit;
    
    // Establish postconditions
    assert forall j :: 0 <= j < n - 1 ==> ProfitForDay(prices, j, c) <= result;
    
    if result == 0 {
        assert forall j :: 0 <= j < n - 1 ==> ProfitForDay(prices, j, c) <= 0;
    } else {
        assert exists j :: 0 <= j < n - 1 && ProfitForDay(prices, j, c) == result;
    }
}
// </vc-code>

