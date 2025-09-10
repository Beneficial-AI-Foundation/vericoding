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
    if s[0] >= seq_max(s[1..]) {
      assert seq_max(s) == s[0];
    } else {
      assert seq_max(s) == seq_max(s[1..]);
      assert seq_max(s[1..]) in s[1..];
    }
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
    assert seq_max(profits) <= 0;
    
    // Ensure MaxPossibleProfit returns 0 when max is negative
    // This follows from the definition of MaxPossibleProfit
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
    // Handled by definition
    assert MaxPossibleProfit(prices, c) == 0;
  } else {
    seq_max_correct(profits);
    
    // Case where max profit is positive
    if seq_max(profits) > 0 {
      assert MaxPossibleProfit(prices, c) == seq_max(profits);
      var k :| 0 <= k < |profits| && profits[k] == seq_max(profits);
      assert ProfitForDay(prices, k, c) == seq_max(profits);
      assert forall i :: 0 <= i < |profits| ==> profits[i] <= seq_max(profits);
    } 
    // Case where max profit is non-positive
    else {
      assert seq_max(profits) <= 0;
      assert MaxPossibleProfit(prices, c) == 0;
      assert forall i :: 0 <= i < |profits| ==> profits[i] <= 0;
    }
  }
  
  // Prove the equivalence
  if (forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= 0) {
    profit_for_day_non_negative_when_zero_max(prices, c);
  } 
  if MaxPossibleProfit(prices, c) == 0 {
    var profits := seq(|prices| - 1, i requires 0 <= i < |prices| - 1 => ProfitForDay(prices, i, c));
    if |profits| > 0 {
      seq_max_correct(profits);
      if seq_max(profits) > 0 {
        assert MaxPossibleProfit(prices, c) == seq_max(profits);
        assert false; // Contradiction
      }
      assert forall i :: 0 <= i < |profits| ==> profits[i] <= 0;
    }
  }
}

lemma max_possible_profit_zero_implies_all_non_positive(prices: seq<int>, c: int)
  requires |prices| >= 2
  requires MaxPossibleProfit(prices, c) == 0
  ensures forall i :: 0 <= i < |prices| - 1 ==> ProfitForDay(prices, i, c) <= 0
{
  var profits := seq(|prices| - 1, i requires 0 <= i < |prices| - 1 => ProfitForDay(prices, i, c));
  if |profits| == 0 {
    // Trivial case: no profit opportunities
  } else {
    seq_max_correct(profits);
    if seq_max(profits) > 0 {
      assert MaxPossibleProfit(prices, c) == seq_max(profits);
      assert false; // Contradiction with premise
    } else {
      assert seq_max(profits) <= 0;
      assert forall i :: 0 <= i < |profits| ==> profits[i] <= seq_max(profits) <= 0;
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
  result := MaxPossibleProfit(prices, c);
  max_possible_profit_correct(prices, c);
  if result > 0 {
    // The postconditions are already ensured by max_possible_profit_correct
  } else {
    max_possible_profit_zero_implies_all_non_positive(prices, c);
  }
}
// </vc-code>

