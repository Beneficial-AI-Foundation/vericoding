// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn unnecessary_cards_count(sorted: Seq<int>, k: int) -> int
  recommends
    forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] >= sorted[j],
    forall|i: int| 0 <= i < sorted.len() ==> sorted[i] >= 1,
    k >= 1
{
  if sorted.len() == 0 {
    0
  } else {
    unnecessary_cards_count_helper(sorted, k, 0, 0, 0)
  }
}

spec fn unnecessary_cards_count_helper(sorted: Seq<int>, k: int, temp: int, ans: int, i: int) -> int
  recommends
    forall|x: int, y: int| 0 <= x < y < sorted.len() ==> sorted[x] >= sorted[y],
    forall|x: int| 0 <= x < sorted.len() ==> sorted[x] >= 1,
    k >= 1,
    0 <= i <= sorted.len(),
    temp >= 0,
    ans >= 0
  decreases sorted.len() - i
{
  if i >= sorted.len() {
    ans
  } else {
    let x = sorted[i];
    if temp + x < k {
      unnecessary_cards_count_helper(sorted, k, temp + x, ans + 1, i + 1)
    } else {
      unnecessary_cards_count_helper(sorted, k, 0, 0, i + 1)
    }
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed map function to take index and element */
exec fn unnecessary_cards_count_helper_exec(sorted: &Vec<i8>, k: i8, temp: i32, ans: i32, i: usize) -> (res: i32)
  requires
    sorted.len() <= 255,
    k >= 1,
    forall|i: int| 0 <= i < sorted.len() ==> sorted[i] as int >= 1,
    i <= sorted.len(),
    temp >= 0,
    ans >= 0
  ensures
    res == unnecessary_cards_count_helper(sorted@.map(|i: int, x: i8| x as int), k as int, temp as int, ans as int, i as int)
{
  if i >= sorted.len() {
    ans
  } else {
    let x = sorted[i] as i32;
    if temp + x < (k as i32) {
      unnecessary_cards_count_helper_exec(sorted, k, temp + x, ans + 1, i + 1)
    } else {
      unnecessary_cards_count_helper_exec(sorted, k, 0, 0, i + 1)
    }
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: i8)
  requires
    n >= 1,
    k >= 1,
    a.len() == n as usize,
    forall|i: int| 0 <= i < a.len() ==> a[i] as int >= 1
  ensures
    result >= 0,
    result as int <= n as int,
    exists|sorted: Seq<int>|
      sorted.len() == a@.len() &&
      sorted.to_multiset() == a@.map(|i: int, x: i8| x as int).to_multiset() &&
      (forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] >= sorted[j]) &&
      (forall|i: int| 0 <= i < sorted.len() ==> sorted[i] >= 1) &&
      result as int == unnecessary_cards_count(sorted, k as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed compilation error by using sort_by with descending order */
  let mut sorted = a.clone();
  sorted.sort_by(|a, b| b.cmp(a)); // sort in descending order
  assert(sorted@.to_multiset() == a@.to_multiset());
  assert(forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] as int >= sorted@[j] as int);
  let result_exec = unnecessary_cards_count_helper_exec(&sorted, k, 0, 0, 0) as i8;
  result_exec
}
// </vc-code>


}

fn main() {}