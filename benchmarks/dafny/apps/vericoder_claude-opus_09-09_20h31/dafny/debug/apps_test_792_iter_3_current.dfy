predicate ValidInput(n: int, d: int, transactions: seq<int>)
{
  n >= 1 && d >= 1 &&
  |transactions| == n &&
  forall i :: 0 <= i < n ==> -10000 <= transactions[i] <= 10000
}

function prefix_sum(transactions: seq<int>, index: int): int
  requires 0 <= index < |transactions|
{
  if index == 0 then transactions[0]
  else prefix_sum(transactions, index - 1) + transactions[index]
}

function count_zero_transactions(transactions: seq<int>): int
{
  if |transactions| == 0 then 0
  else (if transactions[0] == 0 then 1 else 0) + count_zero_transactions(transactions[1..])
}

function balance_after_day(transactions: seq<int>, deposits: seq<int>, day: int): int
  requires 0 <= day < |transactions|
  requires |deposits| == |transactions|
{
  if day == 0 then deposits[0] + transactions[0]
  else balance_after_day(transactions, deposits, day - 1) + deposits[day] + transactions[day]
}

function count_positive_deposits(deposits: seq<int>): int
{
  if |deposits| == 0 then 0
  else (if deposits[0] > 0 then 1 else 0) + count_positive_deposits(deposits[1..])
}

predicate valid_deposits_schedule(transactions: seq<int>, d: int, deposits_schedule: seq<int>, num_deposits: int)
  requires |deposits_schedule| == |transactions|
  requires forall i :: 0 <= i < |deposits_schedule| ==> deposits_schedule[i] >= 0
{
  num_deposits == count_positive_deposits(deposits_schedule) &&
  forall i :: 0 <= i < |transactions| ==> 
    (deposits_schedule[i] > 0 ==> transactions[i] == 0)
}

function filter_positive(deposits: seq<int>): seq<int>
{
  if |deposits| == 0 then []
  else if deposits[0] > 0 then [deposits[0]] + filter_positive(deposits[1..])
  else filter_positive(deposits[1..])
}

// <vc-helpers>
lemma balance_monotonic(transactions: seq<int>, deposits: seq<int>, day1: int, day2: int)
  requires 0 <= day1 < day2 < |transactions|
  requires |deposits| == |transactions|
  requires forall i :: 0 <= i < |deposits| ==> deposits[i] >= 0
  ensures balance_after_day(transactions, deposits, day1) <= balance_after_day(transactions, deposits, day2)
{
  // The balance increases monotonically with non-negative deposits and transactions
  // This follows from the recursive definition of balance_after_day
  if day1 == day2 - 1 {
    assert balance_after_day(transactions, deposits, day2) == 
           balance_after_day(transactions, deposits, day1) + deposits[day2] + transactions[day2];
    assert deposits[day2] >= 0;
  } else {
    balance_monotonic(transactions, deposits, day1, day2 - 1);
    assert balance_after_day(transactions, deposits, day2) == 
           balance_after_day(transactions, deposits, day2 - 1) + deposits[day2] + transactions[day2];
    assert deposits[day2] >= 0;
  }
}

function sum_range(s: seq<int>, start: int, end: int): int
  requires 0 <= start <= end <= |s|
  decreases end - start
{
  if start == end then 0
  else s[start] + sum_range(s, start + 1, end)
}

function min_deposit_needed(current_balance: int, next_transaction: int): int
{
  if current_balance + next_transaction < 0 then
    -(current_balance + next_transaction)
  else
    0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, transactions: seq<int>) returns (result: int)
  requires ValidInput(n, d, transactions)
  ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
  var deposits := seq(n, i => 0);
  var current_balance := 0;
  var num_deposits := 0;
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |deposits| == n
    invariant forall j :: 0 <= j < n ==> deposits[j] >= 0
    invariant forall j :: 0 <= j < i ==> (deposits[j] > 0 ==> transactions[j] == 0)
    invariant i > 0 ==> current_balance >= 0
    invariant num_deposits >= 0
    invariant num_deposits <= d
    invariant i > 0 ==> current_balance == balance_after_day(transactions, deposits, i-1)
  {
    if transactions[i] == 0 {
      // Can make a deposit on this day if needed
      var needed := min_deposit_needed(current_balance, 0);
      
      // Look ahead to find maximum deposit needed
      var lookahead_balance := current_balance;
      var j := i;
      while j < n && transactions[j] == 0
        invariant i <= j <= n
        invariant lookahead_balance >= current_balance + sum_range(transactions, i, j)
      {
        lookahead_balance := lookahead_balance + transactions[j];
        if lookahead_balance < 0 {
          var temp_needed := -lookahead_balance;
          if temp_needed > needed {
            needed := temp_needed;
          }
        }
        j := j + 1;
      }
      
      if needed > 0 {
        if num_deposits >= d {
          return -1;
        }
        deposits := deposits[i := needed];
        num_deposits := num_deposits + 1;
        current_balance := current_balance + needed;
      }
    }
    
    current_balance := current_balance + transactions[i];
    
    if current_balance < 0 {
      return -1;
    }
    
    i := i + 1;
  }
  
  if num_deposits > d {
    return -1;
  }
  
  return num_deposits;
}
// </vc-code>

