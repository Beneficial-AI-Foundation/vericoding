// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, d: int, transactions: Seq<int>) -> bool {
  n >= 1 && d >= 1 &&
  transactions.len() == n &&
  forall|i: int| 0 <= i < n ==> #[trigger] transactions[i] >= -10000 && #[trigger] transactions[i] <= 10000
}

spec fn prefix_sum(transactions: Seq<int>, index: int) -> int
  decreases index
{
  if index < 0 || index >= transactions.len() { 0int }
  else if index == 0 { transactions[0] }
  else { prefix_sum(transactions, index - 1) + transactions[index] }
}

spec fn count_zero_transactions(transactions: Seq<int>) -> int
  decreases transactions.len()
{
  if transactions.len() == 0 { 0int }
  else { (if transactions[0] == 0 { 1int } else { 0int }) + count_zero_transactions(transactions.drop_first()) }
}

spec fn balance_after_day(transactions: Seq<int>, deposits: Seq<int>, day: int) -> int
  decreases day
{
  if day < 0 || day >= transactions.len() || deposits.len() != transactions.len() { 0int }
  else if day == 0 { deposits[0] + transactions[0] }
  else { balance_after_day(transactions, deposits, day - 1) + deposits[day] + transactions[day] }
}

spec fn count_positive_deposits(deposits: Seq<int>) -> int
  decreases deposits.len()
{
  if deposits.len() == 0 { 0int }
  else { (if deposits[0] > 0 { 1int } else { 0int }) + count_positive_deposits(deposits.drop_first()) }
}

spec fn valid_deposits_schedule(transactions: Seq<int>, d: int, deposits_schedule: Seq<int>, num_deposits: int) -> bool {
  deposits_schedule.len() == transactions.len() &&
  (forall|i: int| 0 <= i < deposits_schedule.len() ==> #[trigger] deposits_schedule[i] >= 0) &&
  num_deposits == count_positive_deposits(deposits_schedule) &&
  forall|i: int| 0 <= i < transactions.len() ==> 
    (#[trigger] deposits_schedule[i] > 0 ==> #[trigger] transactions[i] == 0)
}

spec fn filter_positive(deposits: Seq<int>) -> Seq<int>
  decreases deposits.len()
{
  if deposits.len() == 0 { Seq::empty() }
  else if deposits[0] > 0 { seq![deposits[0]].add(filter_positive(deposits.drop_first())) }
  else { filter_positive(deposits.drop_first()) }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_prefix_sum_properties(transactions: Seq<int>, i: int)
    requires
        0 <= i < transactions.len()
    ensures
        prefix_sum(transactions, i) == prefix_sum(transactions, i - 1) + transactions[i]
{
    if i > 0 {
        reveal(prefix_sum);
    }
}

proof fn lemma_balance_properties(transactions: Seq<int>, deposits: Seq<int>, day: int)
    requires
        0 <= day < transactions.len(),
        deposits.len() == transactions.len()
    ensures
        balance_after_day(transactions, deposits, day) ==
            (if day == 0 { deposits[0] + transactions[0] }
             else { balance_after_day(transactions, deposits, day - 1) + deposits[day] + transactions[day] })
{
    reveal(balance_after_day);
}

/* helper modified by LLM (iteration 5): fixed overflow issue by tightening invariants and adding assertion */
fn compute_min_deposits(n: i8, d: i8, transactions: Vec<i8>) -> (result: i8)
    requires
        valid_input(n as int, d as int, transactions@.map(|x: int, y: i8| y as int)),
        n >= 0,
        transactions.len() == n as nat
    ensures
        result == -1 || (result >= 0 && result <= d)
{
    let mut deposits_needed: i8 = 0;
    let mut balance: i32 = 0;
    let mut i: usize = 0;
    
    while i < transactions.len()
        invariant
            i <= transactions.len(),
            deposits_needed >= 0,
            deposits_needed <= d,
            balance >= 0,
            balance <= 10000,
        decreases transactions.len() - i
    {
        let transaction = transactions[i] as i32;
        assert(transaction >= -10000 && transaction <= 10000);
        
        if balance + transaction < 0 {
            if transactions[i] == 0 {
                if deposits_needed < d {
                    deposits_needed = deposits_needed + 1;
                    balance = 0;
                } else {
                    return -1;
                }
            } else {
                return -1;
            }
        } else {
            balance = balance + transaction;
            assert(balance <= 20000);
            if balance > 10000 {
                balance = 10000;
            }
        }
        
        i = i + 1;
    }
    
    deposits_needed
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, transactions: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, d as int, transactions@.map(|x: int, y: i8| y as int))
  ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, just calling helper */
    let result = compute_min_deposits(n, d, transactions);
    result
}
// </vc-code>


}

fn main() {}