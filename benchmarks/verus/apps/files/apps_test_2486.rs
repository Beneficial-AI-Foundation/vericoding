// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, a: Seq<int>) -> (result: int)
  requires
    n >= 1,
    k >= 1,
    a.len() == n,
    forall|i: int| 0 <= i < a.len() ==> a[i] >= 1
  ensures
    result >= 0,
    result <= n,
    exists|sorted: Seq<int>|
      sorted.len() == a.len() &&
      sorted.to_multiset() == a.to_multiset() &&
      (forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] >= sorted[j]) &&
      (forall|i: int| 0 <= i < sorted.len() ==> sorted[i] >= 1) &&
      result == unnecessary_cards_count(sorted, k)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}