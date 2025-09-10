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
lemma seq_max_correct(s: seq<int>)
  requires |s| > 0
  ensures seq_max(s) in s
  ensures forall i :: 0 <= i < |s| ==> s[i] <= seq_max(s)
{
  if |s| == 1 {
    // Base case: singleton sequence
  } else {
    seq_max_correct(s[1..]);
    // The maximum is either the first element or max of the rest
  }
}

lemma seq_max_non_negative_if_all_non_negative(s: seq<int>)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures seq_max(s) >= 0
{
  seq_max_correct(s);
}

lemma profit_for_day_non_negative_when_zero_max(prices: seq<int>, c: int)
  requires |prices| >= 2
  requires (forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= 0)
  ensures MaxPossibleProfit(prices, c) == 0
{
  var profits := seq(|prices| - 1, i requires 0 <= i < |prices| - 1 => ProfitForDay(prices, i, c));
  
  if |profits| == 0 {
    // Empty case already handled by MaxPossibleProfit
  } else {
    seq_max_correct(profits);
    assert forall i :: 0 <= i < |profits| ==> profits[i] <= 0;
    
    // Also need to show that max is at least 0 when all are <= 0
    if exists i :: 0 <= i < |profits| && profits[i] == 0 {
      assert seq_max(profits) >= 0;
      assert seq_max(profits) <= 0;
      assert seq_max(profits) == 0;
    } else {
      assert forall i :: 0 <= i < |profits| ==> profits[i] < 0;
      // If all profits are negative, we need to show max is non-negative
      assert profits[0] < 0;
      assert |profits| > 0;
      assert seq_max(profits) < 0;
      assert 0 >= seq_max(profits);
    }
  }
}

lemma max_possible_profit_correct(prices: seq<int>, c: int)
  requires |prices| >= 2
  ensures MaxPossibleProfit(prices, c) >= 0
  ensures MaxPossibleProfit(prices, c) == 0 <==> (forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= 0)
  ensures MaxPossibleProfit(prices, c) > 0 ==> (exists i :: 0 <= i < |prices| - 1 && ProfitForDay(prices, i, c) == MaxPossibleProfit(prices, c))
  ensures forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= MaxPossibleProfit(prices, c)
{
  var profits := seq(|prices| - 1, i requires 0 <= i < |prices| - 1 => ProfitForDay(prices, i, c));
  
  if |profits| == 0 {
    assert MaxPossibleProfit(prices, c) == 0;
    assert forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= 0;
  } else {
    seq_max_correct(profits);
    
    if |profits| == 1 {
      if profits[0] <= 0 {
        assert MaxPossibleProfit(prices, c) == 0;
      } else {
        assert MaxPossibleProfit(prices, c) == profits[0];
      }
    } else {
      assert MaxPossibleProfit(prices, c) == seq_max(profits);
    }
  }
  
  // Prove the equivalence
  if (forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= 0) {
    profit_for_day_non_negative_when_zero_max(prices, c);
  } 
  else if MaxPossibleProfit(prices, c) == 0 {
    var profits := seq(|prices| - 1, i requires 0 <= i < |prices| - 1 => ProfitForDay(prices, i, c));
    seq_max_correct(profits);
    assert seq_max(profits) == 0;
    assert forall i :: 0 <= i < |profits| ==> profits[i] <= 0;
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
  max_possible_profit_correct(prices, c);
  result := MaxPossibleProfit(prices, c);
  if (result > 0) {
    assert exists i :: 0 <= i < |prices| - 1 && ProfitForDay(prices, i, c) == result;
  } else {
    assert forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= 0;
  }
}
// </vc-code>

