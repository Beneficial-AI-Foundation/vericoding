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
       ( transactions[0] != 0 && CanReachZero(sub_transactions[1..], num_deposits_left) ) ||
       ( transactions[0] == 0 && num_deposits_left > 0 && CanReachZero(sub_transactions[1..], num_deposits_left - 1) )
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

  var max_possible_balance := 0;
  var current_balance := 0;
  var deposits_used := 0;
  var last_zero_day_streak_start := -1; // Index of the start of the current streak of zero-transaction days

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant deposits_used <= d
    invariant max_possible_balance >= current_balance
    invariant current_balance == (sum k :: 0 <= k < i :: transactions[k]) + (sum k :: 0 <= k < i && transactions[k] == 0 && k >= last_zero_day_streak_start :: 1)
    invariant deposits_used == (sum k :: 0 <= k < i && transactions[k] == 0 && k >= last_zero_day_streak_start :: 1) // deposits used for a streak of zeros for balance
    invariant last_zero_day_streak_start == -1 || (0 <= last_zero_day_streak_start < i && transactions[last_zero_day_streak_start] == 0)
  {
    if transactions[i] != 0 {
      current_balance := current_balance + transactions[i];
      last_zero_day_streak_start := -1; // Reset streak
    } else { // transactions[i] == 0
      if last_zero_day_streak_start == -1 {
        last_zero_day_streak_start := i;
      }
      current_balance := current_balance + 0 + 1; // deposit 1 to cover the zero
      deposits_used := deposits_used + 1;
    }
    
    // The problem statement says "total debt incurred" should be minimized.
    // This implies minimizing the maximum negative balance.
    // If the current balance plus remaining deposits (d - deposits_used) is negative, it is impossible to reach zero.
    // However, the problem simplifies and constraints that a deposit must be 1. So, we make the balance zero.
    // What if the balance is currently negative and we have more deposits? We "spend" them to cover negatives.
    // This isn't really "current_balance", but the balance "after" using minimal deposits.
    // Let's rethink.

    // max_possible_balance is the maximum balance we could have, using all remaining deposits.
    // This is not what we want. We want the maximum (least negative) balance across all days *after*
    // assigning deposits such that the final balance is 0.
    // The "greedy strategy" for min-max balance is not to deposit until a negative balance.

    // Let's re-evaluate the greedy strategy:
    // When transactions[i] != 0: current_total_value += transactions[i]
    // When transactions[i] == 0: Increment current_total_value. We must cover it.
    // Track the deficit. We have `d` deposits.
    // The total value needed is `sum(transactions)` + `count_zero_transactions`.
    // If this total is >= 0 and <= d then we can make it 0.

    // Let's use `current_running_sum`
    var current_running_sum := (sum k :: 0 <= k <= i :: transactions[k]);
    var zeros_up_to_i := count_zero_transactions(transactions[0 .. i+1]);

    // Check if it's possible to maintain non-negative balance considering only *necessary* deposits so far
    if current_running_sum + zeros_up_to_i - (d - (min_deposits_needed - zeros_up_to_i)) < 0 {
      // This is complicated. We have `d` deposits, `min_deposits_needed` are required.
      // We have `d - min_deposits_needed` "extra" deposits.
      // These extra deposits can be used to convert any transactions[j] != 0 to transactions[j] + 1.
      // To minimize the maximum negative balance, these extra deposits should be used on days with negative transactions,
      // or to boost balance before a very negative day.

      // A simple check is to see if, at any point, the prefix sum of transactions,
      // along with the minimum necessary deposits to cover zeros up to this point,
      // *and* *all* available extra deposits, would still render the balance negative.
      // This would mean it's impossible.

      // If at any point, the sum of transactions up to day `i` plus the number of zero transactions up to day `i`,
      // exceeds `d`, then we cannot cover all zero transactions.
      if zeros_up_to_i > d { // This is covered by early min_deposits_needed check.
        // It's possible that earlier min_deposits_needed check passes, but at some intermediate point,
        // we can't sustain the balance due to temporary negative sums.
        // This problem needs the *minimum* total debt incurred.
        // This is equivalent to finding the maximum negative value of `prefix_sum(transactions, i) + CountZeros(transactions[0..i]) - deposits_used_so_far`.
        // where `deposits_used_so_far` is effectively the number of zeros encountered when we *have* to make a deposit.
      }
    }
    
    // Consider the conceptual balance if we only paid for zeros.
    // `current_balance` for this loop will track `prefix_sum(transactions, i) + count_zeros_in_prefix`
    // where `count_zeros_in_prefix` is the count of zeros in `transactions[0..i]`.
    // If this goes below zero at any point, we have a problem.
    // We have `d - count_zero_transactions(transactions)` 'spare' deposits.
    
    current_balance := prefix_sum(transactions, i) + count_zero_transactions(transactions[0..i+1]);
    
    // Add remaining spare deposits if needed
    // The `d` available deposits have two uses:
    // 1. Convert `transactions[i] == 0` to `transactions[i] == 1`
    // 2. Add `1` to `transactions[i] != 0` to alleviate negative balance.
    
    // We need to find `min(max_negative_balance)` over all valid deposit schedules.
    // A valid deposit schedule uses exactly `min_deposits_needed` deposits for the zeros,
    // and `d - min_deposits_needed` for other days.

    max_possible_balance := (sum k :: 0 <= k <= i :: transactions[k]) + count_zero_transactions(transactions[0..i+1]);
    
    if max_possible_balance < 0 {
      // If even with the bare minimum deposits for zeros, our balance goes negative,
      // we need to consider using the spare deposits to boost the balance.
      // The spare deposits (d - min_deposits_needed) should be used greedily on the most negative days
      // (or to prevent the largest negative drop).
      // This looks like a variation of a maximum subarray sum problem, or a heap-based approach.

      // For minimizing the maximum debt, we use a slightly different "running balance".
      // We process transactions, adding `transactions[i]`. If `transactions[i] == 0`, we add 1.
      // If the running balance becomes negative, we need to use one of the `d` deposits.
      // We should use an "extra" deposit to bring the balance back to 0.
      // To minimize `max_debt`, we should use extra deposits (if available) when the balance is most negative.

      // Let `current_effective_balance` be `prefix_sum(transactions, i) + (number of zeros in prefix i)`.
      // Let `deficits_covered_by_extra_deposits` be an additional amount we add when the balance is falling.

      // This problem can be modeled by tracking the current balance.
      // When `transactions[i] == 0`, we are forced to spend one of `d` deposits.
      // When `transactions[i] != 0`, we can optionally spend a deposit.
      // To minimize the maximum debt incurred, we should greedily use deposits.
      // We use a min-priority queue to keep track of previous negative additions.

      // We maintain `current_debt = current_running_sum + current_deposits_spent`.
      // We wish to make this as non-negative as possible.
      // The `d` deposits can be spent at any point.

      // This is a known variant. Let's use the approach from similar problems:
      // Track `current_balance`. When `transactions[i] == 0`, `current_balance += 1`.
      // If `transactions[i] != 0`, `current_balance += transactions[i]`.
      // If `current_balance < 0`, we *must* spend a deposit. Greedily use it on the most negative `transactions[j]` encountered so far.
      // Store negative transactions in a min-priority queue (or a multiset).
      // `deposits_available = d`
      // `current_balance = 0`
      // `max_debt = 0`

      // A simple check on whether it's possible to reach non-negative balance from day 0 to day i
      // `current_balance = prefix_sum(transactions, i)`
      // `zeros_to_cover = count_zero_transactions(transactions[0..i+1])`
      // `deposits_to_cover_zeros = min(d, zeros_to_cover)`
      // `remaining_deposits = d - deposits_to_cover_zeros` // these are available to cover other negative transactions
      
      // Let's restart with a standard approach for this type of problem:
      // Simulate with the minimum required deposits, and use spare deposits to fix deficits.
      
      // `current_balance` will be the balance after transactions and required zero-deposits
      // `pq` will store the values of `transactions[k]` that represent "deficits" we might cover with spare deposits.
      
      var effective_balance := 0; // Balance assuming all zeros are covered by 1s (using d deposits)
      var max_debt_incurred := 0; // This will track the most negative `effective_balance` seen

      var used_zero_deposits := 0;
      var pq := new Multiset<int>(); // To store values that we temporarily consider as negative contributions

      for k := 0 to n - 1
        invariant 0 <= k <= n
        invariant used_zero_deposits <= d
        invariant effective_balance == (sum l :: 0 <= l < k :: transactions[l]) + (sum l :: 0 <= l < k && transactions[l] == 0 && used_zero_deposits <= d :: 1) - (sum x | x in pq :: x) // roughly
        invariant forall x | x in pq :: x <= 0 // We track negative contributions, or 0 for zero-days that were covered
        invariant pq.cardinality <= d - used_zero_deposits + (count l :: 0 <= l < k && transactions[l] == 0 :: 1) // upper bound on what can be in PQ related to deposits

      {
        if transactions[k] == 0 {
          if used_zero_deposits < d {
            effective_balance := effective_balance + 1; // Used a forced deposit
            used_zero_deposits := used_zero_deposits + 1;
            pq := pq + Multiset{0}; // Mark that we spent a deposit here.
          } else {
            // Cannot cover this zero, impossible to reach 0 final balance if we strictly need to cover *all* zeros
            // This is actually incorrect. We have `d` deposits total.
            // Some are for `transactions[k] == 0`, others for `transactions[k] < 0`.
            return -1; // If `d` is less than `count_zero_transactions`, then it's impossible.
                       // This check `min_deposits_needed > d` is done at the beginning.
                       // So `used_zero_deposits` can't exceed `d` here.
            // However, the `pq` logic will ensure `d` is respected.
          }
        } else {
          effective_balance := effective_balance + transactions[k];
          if transactions[k] < 0 {
            pq := pq + Multiset{transactions[k]};
          }
        }

        // If at any point the balance (with all zero-transactions covered)
        // becomes negative, we must use one of our *spare* deposits
        // to mitigate the most negative transaction seen so far (from `pq`).
        while effective_balance < 0 && pq.cardinality > 0 && (used_zero_deposits < d || (exists x in pq :: x == 0)) {
            // We need to find the element in pq that contributes most negatively
            // (either a `transactions[k]` that's very negative, or a `0` from a zero-day deposit that we can "reallocate").
            // We should pick the smallest element in `pq` (most negative).
            var min_val := 0;
            if pq.cardinality > 0 {
              min_val := (min x | x in pq :: x);
            }

            if min_val < 0 || (min_val == 0 && (used_zero_deposits + (count x | x in pq && x == 0 :: 1) > count_zero_transactions(transactions))) {
               // This means we have a negative transaction we can "undo" with a deposit,
               // or a zero-day deposit that we can conceptually swap for an earlier negative.

              // We need to use one of `d` deposits to fix debt.
              // Which `transaction[x]` to undo? The one that is currently making `effective_balance` the lowest.
              // This logic with `pq` is standard for minimizing the peak debt.
              // We find the smallest element, convert it to `1`, and add to `effective_balance`.
              
              // Find the largest (least negative) magnitude negative element
              var max_negative_val := (max x | x in pq && x <= 0 :: x); // Should be `min` but logic below implies removing largest deficit
              
              // The problem here is that `pq` contains `transactions[k]` or `0` for zero days.
              // When `effective_balance` goes negative, we use a deposit.
              // We replace the largest negative contribution with +1 (or make it less negative by 1).
              
              // We just say `effective_balance` increases by `1` and we mark a deposit as used.
              // The `pq` stores the *original* transaction value.
              // When `effective_balance` drops below 0, it means we must apply one of the `d` deposits.
              // To minimize `max_debt_incurred`, we should apply the deposit to the `transactions[k]`
              // that had the largest (most positive) value that we previously considered as negative (i.e. `max x` in `pq`)
              // effectively making `transactions[k] + 1` instead of `transactions[k]`.
              
              // This is usually done by adding `transactions[k]` to `pq`.
              // If `effective_balance + transactions[k] < 0` for this `k`,
              // and `deposits_available > 0`, we remove the smallest element from `pq`.
              // Add `1` to balance. Replace smallest `PQ` value with `1`.
              
              
              // Let us simplify: `effective_balance` accumulates transactions.
              // If `transactions[k] == 0`, we are *forced* to use a deposit. `effective_balance += 1`.
              // If `effective_balance` drops below 0, and we have *spare* deposits (`d - used_zero_deposits`),
              // we can use a spare deposit to increase `effective_balance` by 1.
              // To minimize `max_debt`, we use this spare deposit to make the lowest-valued deposit so far.
              // So, if we see `transactions[k] == X`, and later `current_balance` is negative,
              // we "spend" an extra deposit by effectively changing `X` to `X+1`.
              // We store `X` in a heap, and when `balance` is negative, we pick the `min_element` of the heap,
              // and add 1 more to it (`min_element + 1`). This is equivalent to `balance += 1`.
              // The value we take from the heap is `min_element` and replace with `min_element + 1`. This effectively means `balance -= min_element`, `balance += (min_element + 1)`. So `balance += 1`.

              // We need `d` total deposits.
              // Let `total_deposits_used_for_fix` be `0`.
              // `balance = 0`.
              // For `k` from `0` to `n-1`:
              //   If `transactions[k] == 0`:
              //      `balance += 1`. `total_deposits_used_for_fix += 1`. `Add(0)` to `pq`.
              //   Else:
              //      `balance += transactions[k]`. `Add(transactions[k])` to `pq` (only if negative for this strategy?)
              //   While `balance < 0` and `total_deposits_used_for_fix < d` and `pq` is not empty:
              //      `val_to_fix = pq.extract_min_val()`.
              //      `balance += 1`. (We are using a deposit to make `val_to_fix` less negative)
              //      `total_deposits_used_for_fix += 1`.
              // If `balance < 0` and no more deposits, then it's `impossible`.
              // `max_debt = max(max_debt, -balance)`. // At any point, track the maximum debt

              // We'll use a `Multiset` to simulate a min-priority queue (though not efficient, for Dafny verification it works).
              // Store all `transactions[k]` and `0` for zero days.
              // We prioritize using deposit on `transactions[k] == 0` first.
              // Then, if balance is negative, we use remaining deposits to make the smallest element of `pq` positive (+1).

              // Re-attempting the loop with a more robust logic
              // `current_balance` - this will track what would be the balance if we cover current zeros.
              // `num_deposits_allocated` - total deposits we have committed to use.
              // `pq` - a min-priority queue (represented by Multiset) of `transactions[k]` values we have encountered.
              // When `transactions[k] == 0`, we add `0` to `pq`. This `0` will eventually be +1.
              // When `transactions[k] != 0`, we add `transactions[k]` to `pq`.
              // At each step, if `sum(elements in pq) + deposits_allocated < 0`, we adjust.

              // Let's use the provided `pq` and an `effective_balance` that means 'what it would be if we spend deposits correctly'.
              max_debt_incurred := 0;
              var current_money_balance := 0; // The sum of transactions
              var deposits_spent := 0; // Total deposits used so far, including "forced" and "optional" ones.

              var negative_contributions := new Multiset<int>(); // Max-priority queue for negative numbers

              for m := 0 to n - 1 {
                var transaction_value := transactions[m];

                if transaction_value == 0 {
                  // This `0` requires a deposit.
                  current_money_balance := current_money_balance + 0; // conceptually
                  // we *must* spend a deposit for this zero, if `deposits_spent < d`.
                  // If we don't have enough deposits for all zeros, it's already impossible.
                  // This is checked by `min_deposits_needed > d`.
                  
                  // For the `max_debt` calculation: a zero transaction requires a deposit of 1.
                  // So we treat it as adding `1` to the balance.
                  current_money_balance := current_money_balance + 1;
                  deposits_spent := deposits_spent + 1;
                  negative_contributions := negative_contributions + Multiset{0}; // Treat this '0' as a value that was 'made 1' by a deposit.
                } else {
                  current_money_balance := current_money_balance + transaction_value;
                  if transaction_value < 0 {
                    negative_contributions := negative_contributions + Multiset{transaction_value};
                  }
                }
                
                // If the balance is negative, we need to use a deposit to increase it.
                // We pick the most negative contribution (from `negative_contributions`) and increment it by 1.
                // This has the effect of `current_money_balance := current_money_balance + 1`.
                while current_money_balance < 0 && deposits_spent < d {
                  if negative_contributions.cardinality == 0 {
                   // This should not happen if current_money_balance < 0 and we still have deposits to spend.
                   // It implies the initial total balance without deposits is too low.
                   // The initial sum `prefix_sum(transactions, n-1) + count_zero_transactions(transactions)`
                   // must be non-negative if we are to end at 0.
                   // If the sum is positive, but `current_money_balance` is negative, we can fix it.
                    max_debt_incurred := -current_money_balance; // This means we used all `d` deposits and still negative
                    break;
                  }
                  
                  // Extract the largest negative value (least negative, e.g., -1 is preferred over -10)
                  var max_neg_val_to_fix := (max x | x in negative_contributions :: x);
                  
                  negative_contributions := negative_contributions - Multiset{max_neg_val_to_fix};
                  negative_contributions := negative_contributions + Multiset{max_neg_val_to_fix + 1}; // Effectively spent a deposit on it

                  current_money_balance := current_money_balance + 1; // Used a deposit
                  deposits_spent := deposits_spent + 1;
                }

                // If at this point, `current_money_balance` is still negative, it contributes to `max_debt_incurred`.
                if -current_money_balance > max_debt_incurred {
                  max_debt_incurred := -current_money_balance;
                }
              }

              return max_debt_incurred;
  }
}
// </vc-code>

