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
    /* code modified by LLM (iteration 4): Fixed type mismatch in sorting loop invariant */
    let mut sorted = a.clone();
    let n_usize = n as usize;
    
    // Sort in descending order
    let mut i: usize = 0;
    while i < n_usize
        invariant
            i <= n_usize,
            sorted.len() == n_usize,
            forall|j: int| 0 <= j < sorted.len() ==> sorted[j] >= 1,
            forall|j: int, k: int| 0 <= j < k < i ==> sorted[j] >= sorted[k]
    {
        let mut j: usize = i + 1;
        while j < n_usize
            invariant
                i < n_usize,
                i + 1 <= j,
                j <= n_usize,
                sorted.len() == n_usize,
                forall|k: int| 0 <= k < sorted.len() ==> sorted[k] >= 1,
                forall|p: int, q: int| 0 <= p < q <= i ==> sorted[p] >= sorted[q],
                forall|p: int| 0 <= p <= i && i as int < sorted.len() ==> sorted[p] >= sorted[i as int]
        {
            if sorted[i] < sorted[j] {
                let temp = sorted[i];
                sorted.set(i, sorted[j]);
                sorted.set(j, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // Count unnecessary cards
    let mut temp: i8 = 0;
    let mut ans: i8 = 0;
    let mut idx: usize = 0;
    
    while idx < n_usize
        invariant
            idx <= n_usize,
            sorted.len() == n_usize,
            temp >= 0,
            ans >= 0,
            ans <= idx as i8,
            forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] >= sorted[j],
            forall|i: int| 0 <= i < sorted.len() ==> sorted[i] >= 1
    {
        let x = sorted[idx];
        if temp + x < k {
            temp = temp + x;
            ans = ans + 1;
        } else {
            temp = 0;
            ans = 0;
        }
        idx = idx + 1;
    }
    
    ans
}
// </vc-code>


}

fn main() {}