// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, d: int, transactions: Seq<int>) -> bool {
    n >= 1 && d >= 1 &&
    transactions.len() == n &&
    forall|i: int| 0 <= i < n ==> -10000 <= transactions[i] <= 10000
}

spec fn prefix_sum(transactions: Seq<int>, index: int) -> int {
    if index == 0 {
        transactions[0]
    } else {
        prefix_sum(transactions, index - 1) + transactions[index]
    }
}

spec fn count_zero_transactions(transactions: Seq<int>) -> int {
    if transactions.len() == 0 {
        0int
    } else {
        (if transactions[0] == 0 { 1int } else { 0int }) + count_zero_transactions(transactions.subrange(1, transactions.len() as int))
    }
}

spec fn balance_after_day(transactions: Seq<int>, deposits: Seq<int>, day: int) -> int {
    if day == 0 {
        deposits[0] + transactions[0]
    } else {
        balance_after_day(transactions, deposits, day - 1) + deposits[day] + transactions[day]
    }
}

spec fn count_positive_deposits(deposits: Seq<int>) -> int {
    if deposits.len() == 0 {
        0int
    } else {
        (if deposits[0] > 0 { 1int } else { 0int }) + count_positive_deposits(deposits.subrange(1, deposits.len() as int))
    }
}

spec fn valid_deposits_schedule(transactions: Seq<int>, d: int, deposits_schedule: Seq<int>, num_deposits: int) -> bool {
    num_deposits == count_positive_deposits(deposits_schedule) &&
    forall|i: int| 0 <= i < transactions.len() ==> 
        (deposits_schedule[i] > 0 ==> transactions[i] == 0)
}

spec fn filter_positive(deposits: Seq<int>) -> Seq<int> {
    if deposits.len() == 0 {
        seq![]
    } else if deposits[0] > 0 {
        seq![deposits[0]] + filter_positive(deposits.subrange(1, deposits.len() as int))
    } else {
        filter_positive(deposits.subrange(1, deposits.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, d: int, transactions: Seq<int>) -> (result: int)
    requires valid_input(n, d, transactions)
    ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}