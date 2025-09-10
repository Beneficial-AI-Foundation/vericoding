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
lemma CountPositiveDepositsLemma(deposits: seq<int>)
  ensures count_positive_deposits(deposits) == |filter_positive(deposits)|
  decreases |deposits|
{
  if |deposits| > 0 {
    CountPositiveDepositsLemma(deposits[1..]);
  }
}

lemma BalanceInvariant(transactions: seq<int>, deposits: seq<int>, day: int)
  requires 0 <= day < |transactions|
  requires |deposits| == |transactions|
  requires forall i :: 0 <= i < |deposits| ==> deposits[i] >= 0
  ensures balance_after_day(transactions, deposits, day) >= 0
{
  if day > 0 {
    BalanceInvariant(transactions, deposits, day - 1);
    // Add calculation to help prove the postcondition
    assert balance_after_day(transactions, deposits, day) == balance_after_day(transactions, deposits, day - 1) + deposits[day] + transactions[day];
  } else {
    assert balance_after_day(transactions, deposits, day) == deposits[0] + transactions[0];
  }
}

lemma ZeroTransactionRequirement(transactions: seq<int>, deposits: seq<int>, day: int)
  requires |deposits| == |transactions|
  requires forall i :: 0 <= i < |transactions| ==> deposits[i] > 0 ==> transactions[i] == 0
  requires 0 <= day < |transactions|
  ensures deposits[day] > 0 ==> transactions[day] == 0
{
}

lemma PositiveDepositIfZeroTransaction(transactions: seq<int>, deposits: seq<int>, day: int)
  requires |deposits| == |transactions|
  requires transactions[day] == 0
  requires 0 <= day < |transactions|
  ensures deposits[day] > 0 || deposits[day] == 0
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
  var num_zero_transactions := count_zero_transactions(transactions);
  
  if num_zero_transactions <= d {
    result := 0;
    return;
  }
  
  var required_deposits := num_zero_transactions - d;
  var min_operations := -1;
  var current_operations := 0;
  var left := 0;
  var window_deposits := 0;
  
  while (left < n && transactions[left] != 0)
    invariant left <= n
  {
    left := left + 1;
  }
  
  if left == n {
    result := 0;
    return;
  }
  
  var right := left;
  while (right < n && window_deposits < required_deposits)
    invariant left <= right <= n
    invariant window_deposits >= 0
  {
    if transactions[right] == 0 {
      window_deposits := window_deposits + 1;
    }
    right := right + 1;
  }
  
  if window_deposits < required_deposits {
    result := -1;
    return;
  }
  
  min_operations := right - left;
  
  while (right < n)
    invariant left <= right <= n
    invariant window_deposits >= required_deposits
  {
    left := left + 1;
    while (left < n && transactions[left] != 0)
      invariant left <= n
    {
      left := left + 1;
    }
    
    right := right + 1;
    while (right < n && transactions[right] != 0)
      invariant right <= n
    {
      right := right + 1;
    }
    
    if right < n {
      var current_length := right - left;
      if current_length < min_operations {
        min_operations := current_length;
      }
    }
  }
  
  result := min_operations;
}
// </vc-code>

