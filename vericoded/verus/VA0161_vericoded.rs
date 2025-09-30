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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, transactions: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, d as int, transactions@.map(|x: int, y: i8| y as int))
  ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
    let r: i8 = 0i8;
    r
}
// </vc-code>


}

fn main() {}