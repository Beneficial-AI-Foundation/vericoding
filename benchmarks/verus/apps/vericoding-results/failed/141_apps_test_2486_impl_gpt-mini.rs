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
/* helper modified by LLM (iteration 5): trivial lemma that a sequence equals itself as a multiset */
proof fn lemma_seq_multiset_id(s: Seq<int>)
  ensures
    s.to_multiset() == s.to_multiset(),
{
  proof {
    assert(s.to_multiset() == s.to_multiset());
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
  /* code modified by LLM (iteration 5): selection sort (descending) implemented and compute unnecessary count */
  let mut v = a.clone();
  // selection sort in-place (descending)
  let mut i: usize = 0;
  while i < v.len() {
    let mut max_j: usize = i;
    let mut j: usize = i + 1;
    while j < v.len() {
      if v[j] > v[max_j] {
        max_j = j;
      }
      j += 1;
    }
    if max_j != i {
      let tmp = v[i];
      v[i] = v[max_j];
      v[max_j] = tmp;
    }
    i += 1;
  }
  // compute unnecessary count using sorted vector v
  let mut temp: i32 = 0;
  let mut ans: i32 = 0;
  let mut idx: usize = 0;
  while idx < v.len() {
    let x_i: i32 = v[idx] as i32;
    if temp + x_i < (k as i32) {
      temp += x_i;
      ans += 1;
    } else {
      temp = 0;
    }
    idx += 1;
  }
  ans as i8
}
// </vc-code>


}

fn main() {}