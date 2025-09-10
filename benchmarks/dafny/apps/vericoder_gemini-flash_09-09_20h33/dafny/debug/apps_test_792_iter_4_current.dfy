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
      prefix_sum(s, k - 1) + s[k];
      (sum i :: 0 <= i <= k - 1 :: s[i]) + s[k];
      sum i :: 0 <= i <= k :: s[i];
    }
  } else {
    assert prefix_sum(s, 0) == s[0];
    assert (sum i :: 0 <= i <= 0 :: s[i]) == s[0];
  }
}

// Helper lemma for the invariant on current_money_balance.
// It proves the relationship between current_money_balance and the sum of transactions and deposits.
lemma SumInvariantHelper(transactions: seq<int>, m: int, negative_contributions: Multiset<int>, current_money_balance: int, deposits_spent: int)
  requires 0 <= m <= |transactions|
  requires forall x :: x in negative_contributions ==> x <= 0 // Values in negative_contributions are non-positive
  requires current_money_balance == (sum j :: 0 <= j < m && transactions[j] != 0 :: transactions[j]) + (sum j :: 0 <= j < m && transactions[j] == 0 :: 0) + deposits_spent - (sum k :: k in negative_contributions :: k)
  ensures current_money_balance + (sum k :: k in negative_contributions :: k) == (sum j :: 0 <= j < m && transactions[j] != 0 :: transactions[j]) + (sum j :: 0 <= j < m && transactions[j] == 0 :: 0) + deposits_spent
{
  // The equality is directly from the premise, just rearranged to match the ensures clause.
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
    invariant current_money_balance + (sum k :: k in negative_contributions :: k) == (sum j :: 0 <= j < m && transactions[j] != 0 :: transactions[j]) + (sum j :: 0 <= j < m && transactions[j] == 0 :: 0) + deposits_spent
    invariant forall x :: x in negative_contributions ==> x <= 0 // Values in negative_contributions are non-positive
  {
    var transaction_value := transactions[m];

    if transaction_value == 0 {
      // When transaction_value is 0, we effectively spend a "forced" deposit to cover it.
      // The current_money_balance increases by 1 (due to the deposit) and not by transaction_value (which is 0).
      // This deposit fills the gap caused by the zero transaction.
      // We don't add 0 to negative_contributions to track debt, because 0 transactions don't contribute to debt
      // as long as we put a deposit. Instead, we directly account for the deposit.
      deposits_spent := deposits_spent + 1;
      current_money_balance := current_money_balance + 1; // Used a deposit
      negative_contributions := negative_contributions + Multiset{0}; // Mark that we spent a deposit here.
                                                                     // This 0 represents that balance was incremented by 1 due to deposit.
                                                                     // If this deposit is later "undone" by taking it back, it is like decreasing balance by 1.
    } else {
      current_money_balance := current_money_balance + transaction_value;
      if transaction_value < 0 {
        negative_contributions := negative_contributions + Multiset{transaction_value};
      }
    }
    
    // While current_money_balance is negative and we have deposits left,
    // we use deposits to alleviate the debt. We prioritize alleviating the largest negative contribution.
    while current_money_balance < 0 && deposits_spent < d {
      if negative_contributions.cardinality == 0 {
        // This case should ideally not be reached if current_money_balance < 0 and deposits_spent < d.
        // If current_money_balance is negative, it must be due to some negative `transaction_value` or
        // a `0` transaction that was covered by a deposit. The `negative_contributions` multiset
        // should contain entries reflecting these.
        // If `negative_contributions` is empty, it implies that current_money_balance became negative
        // due to something else than processing transactions, which contradicts the logic.
        break; 
      }
      
      // Extract the largest negative value (closest to zero, e.g., -1 is picked before -10)
      // This is the transaction value that contributed most negatively to the current balance.
      var max_neg_val_to_fix := (max x | x in negative_contributions :: x);
      
      negative_contributions := negative_contributions - Multiset{max_neg_val_to_fix};
      // When we "fix" a negative transaction with a deposit, it's like increasing that transaction's value by 1.
      // So, if we had -5, and we deposit, it becomes -4 effectively concerning its contribution to debt.
      negative_contributions := negative_contributions + Multiset{max_neg_val_to_fix + 1}; // Effectively spent a deposit on it

      current_money_balance := current_money_balance + 1; // Used a deposit
      deposits_spent := deposits_spent + 1;
    }

    if -current_money_balance > max_debt_incurred {
      max_debt_incurred := -current_money_balance;
    }
  }

  return max_debt_incurred;
}
// </vc-code>

