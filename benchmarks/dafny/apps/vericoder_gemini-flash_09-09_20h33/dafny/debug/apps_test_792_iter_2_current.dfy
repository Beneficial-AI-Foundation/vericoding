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
predicate CanReachZero(sub_transactions: seq<int>, num_deposits_left: int)
{
  num_deposits_left >= 0 &&
  (
    (|sub_transactions| == 0 && num_deposits_left == 0) ||
    (|sub_transactions| > 0 &&
     (
       ( sub_transactions[0] != 0 && CanReachZero(sub_transactions[1..], num_deposits_left) ) ||
       ( sub_transactions[0] == 0 && num_deposits_left > 0 && CanReachZero(sub_transactions[1..], num_deposits_left - 1) )
     )
    )
  )
}

function MinDepositsToCover(s: seq<int>): (r: int)
  decreases |s|
  ensures r >= 0
{
  if |s| == 0 then 0
  else if s[0] != 0 then MinDepositsToCover(s[1..])
  else 1 + MinDepositsToCover(s[1..])
}

// Lemma to relate count_zero_transactions to MinDepositsToCover for non-negative transactions
lemma MinDepositsToCoverIsCountZeroTransactions(s: seq<int>)
  ensures MinDepositsToCover(s) == count_zero_transactions(s)
{
  if |s| == 0 {
  } else if s[0] != 0 {
    MinDepositsToCoverIsCountZeroTransactions(s[1..]);
  } else {
    MinDepositsToCoverIsCountZeroTransactions(s[1..]);
  }
}

lemma SumOfPrefixes(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures prefix_sum(s, k) == (sum i :: 0 <= i <= k :: s[i])
{
  if k > 0 {
    SumOfPrefixes(s, k-1);
    calc {
      prefix_sum(s, k);
      { assert k > 0; }
      prefix_sum(s, k - 1) + s[k];
      { reveal SumOfPrefixes(s, k-1); }
      (sum i :: 0 <= i <= k - 1 :: s[i]) + s[k];
      sum i :: 0 <= i <= k :: s[i];
    }
  } else {
    assert prefix_sum(s, 0) == s[0];
    assert (sum i :: 0 <= i <= 0 :: s[i]) == s[0];
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, transactions: seq<int>) returns (result: int)
  requires ValidInput(n, d, transactions)
  ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
  var min_deposits_needed := count_zero_transactions(transactions);
  if min_deposits_needed > d then
    return -1;

  var max_debt_incurred := 0;
  var current_money_balance := 0; // The sum of transactions
  var deposits_spent := 0; // Total deposits used so far, including "forced" and "optional" ones.

  var negative_contributions := new Multiset<int>(); // To simulate a max-priority queue for negative values

  for m := 0 to n - 1
    invariant 0 <= m <= n
    invariant deposits_spent <= d
    invariant max_debt_incurred >= 0
    // Invariant to relate negative_contributions to current_money_balance. Not strictly necessary for fix, but for proof.
    // Invariant current_money_balance == (sum k :: 0 <= k < m && transactions[k] != 0 :: transactions[k] + (if transactions[k] in negative_contributions then 1 else 0)) + (sum k :: 0 <= k < m && transactions[k] == 0 :: 1)
  {
    var transaction_value := transactions[m];

    if transaction_value == 0 {
      current_money_balance := current_money_balance + 1; // Used a forced deposit
      deposits_spent := deposits_spent + 1;
      negative_contributions := negative_contributions + Multiset{0}; // Mark that we spent a deposit here.
    } else {
      current_money_balance := current_money_balance + transaction_value;
      if transaction_value < 0 {
        negative_contributions := negative_contributions + Multiset{transaction_value};
      }
    }
    
    while current_money_balance < 0 && deposits_spent < d {
      if negative_contributions.cardinality == 0 {
        break; // Should not happen if balance is negative and d is available
      }
      
      // Extract the largest negative value (closest to zero, e.g., -1 is picked before -10)
      var max_neg_val_to_fix := (max x | x in negative_contributions :: x);
      
      negative_contributions := negative_contributions - Multiset{max_neg_val_to_fix};
      negative_contributions := negative_contributions + Multiset{max_neg_val_to_fix + 1}; // Effectively spent a deposit on it

      current_money_balance := current_money_balance + 1; // Used a deposit
      deposits_spent := deposits_spent + 1;
    }

    if -current_money_balance > max_debt_incurred {
      max_debt_incurred := -current_money_balance;
    }
  }

  // After the loop, if the final balance is negative, it indicates that even with all deposits,
  // we could not bring it to non-negative. This debt is the final max_debt_incurred.
  // However, the problem asks for the minimum possible maximal debt.
  // This loop already tracks the maximum debt at any point.

  return max_debt_incurred;
}
// </vc-code>

