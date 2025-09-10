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
lemma prefix_sum_property(transactions: seq<int>, i: int)
  requires 0 <= i < |transactions|
  ensures prefix_sum(transactions, i) == (if i == 0 then transactions[0] else prefix_sum(transactions, i-1) + transactions[i])
{
}

lemma count_zero_bound(transactions: seq<int>)
  ensures count_zero_transactions(transactions) <= |transactions|
{
}

lemma count_zero_nonnegative(transactions: seq<int>)
  ensures count_zero_transactions(transactions) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, transactions: seq<int>) returns (result: int)
  requires ValidInput(n, d, transactions)
  ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
  var zero_days := count_zero_transactions(transactions);
  count_zero_nonnegative(transactions);
  
  if zero_days == 0 && prefix_sum(transactions, 0) < 0 {
    return -1;
  }
  
  var balance := 0;
  var deposits_used := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant deposits_used <= zero_days
    invariant balance >= 0
  {
    if transactions[i] == 0 {
      var future_min := balance + transactions[i];
      var j := i + 1;
      while j < n
        invariant i < j <= n
      {
        var temp_balance := future_min;
        var k := i + 1;
        while k <= j
          invariant i + 1 <= k <= j + 1
        {
          temp_balance := temp_balance + transactions[k];
          k := k + 1;
        }
        if temp_balance < future_min {
          future_min := temp_balance;
        }
        j := j + 1;
      }
      
      if future_min < 0 {
        if deposits_used >= zero_days {
          return -1;
        }
        balance := balance - future_min;
        deposits_used := deposits_used + 1;
      }
    }
    
    balance := balance + transactions[i];
    if balance < 0 {
      return -1;
    }
    i := i + 1;
  }
  
  return deposits_used;
}
// </vc-code>

