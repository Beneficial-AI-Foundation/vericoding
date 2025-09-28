// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_ladder(arr: Seq<int>, l: int, r: int) -> bool {
  &&& 0 <= l <= r < arr.len()
  &&& if l == r {
    true
  } else {
    exists|k: int| l <= k <= r && 
      is_non_decreasing(arr, l, k) && 
      is_non_increasing(arr, k, r)
  }
}

spec fn is_non_decreasing(arr: Seq<int>, start: int, end: int) -> bool {
  &&& 0 <= start <= end < arr.len()
  &&& forall|i: int| start <= i < end ==> #[trigger] arr[i] <= arr[i+1]
}

spec fn is_non_increasing(arr: Seq<int>, start: int, end: int) -> bool {
  &&& 0 <= start <= end < arr.len()
  &&& forall|i: int| start <= i < end ==> #[trigger] arr[i] >= arr[i+1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): renamed executable non_decreasing check */
fn check_non_decreasing(arr: &Vec<i8>, start: usize, end: usize) -> (b: bool)
    requires
        0 <= start <= end <= arr@.len(),
    ensures
        b ==> forall|i: usize| start <= i < end ==> #[trigger] (arr@[i] as int) <= arr@[i + 1] as int,
{
    let mut i: usize = start;
    while i < end
        invariant
            start <= i <= end,
            forall|j: usize| start <= j < i ==> #[trigger] (arr@[j] as int) <= arr@[j + 1] as int,
        decreases (end - i),
    {
        if arr[i] > arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    return true;
}

/* helper modified by LLM (iteration 2): renamed executable non_increasing check */
fn check_non_increasing(arr: &Vec<i8>, start: usize, end: usize) -> (b: bool)
    requires
        0 <= start <= end <= arr@.len(),
    ensures
        b ==> forall|i: usize| start <= i < end ==> #[trigger] (arr@[i] as int) >= arr@[i + 1] as int,
{
    let mut i: usize = start;
    while i < end
        invariant
            start <= i <= end,
            forall|j: usize| start <= j < i ==> #[trigger] (arr@[j] as int) >= arr@[j + 1] as int,
        decreases (end - i),
    {
        if arr[i] < arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, arr: Vec<i8>, queries: Vec<(i8, i8)>) -> (results: Vec<Vec<char>>)
  requires 
    n >= 1 && m >= 1,
    arr@.len() == n as int,
    queries@.len() == m as int,
    forall|i: int| 0 <= i < m as int ==> 1 <= #[trigger] queries@[i].0 as int <= queries@[i].1 as int <= n as int,
  ensures 
    results@.len() == m as int,
    forall|i: int| 0 <= i < m as int ==> #[trigger] results@[i]@ == seq!['Y', 'e', 's'] || results@[i]@ == seq!['N', 'o'],
    forall|i: int| 0 <= i < m as int ==> 
      (#[trigger] results@[i]@ == seq!['Y', 'e', 's'] <==> is_ladder(arr@.map(|_i, v| v as int), queries@[i].0 as int - 1, queries@[i].1 as int - 1)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented solve function with renamed helper calls */
{
    let mut results: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < m as usize
        invariant
            0 <= i <= m as usize,
            results@.len() == i,
            forall|j: usize| 0 <= j < i ==> (results@[j]@ == seq!['Y', 'e', 's'] || results@[j]@ == seq!['N', 'o']),
        decreases ((m as usize) - i),
    {
        let q = queries[i];
        let l: usize = (q.0 - 1) as usize;
        let r: usize = (q.1 - 1) as usize;
        let mut is_lad: bool = false;
        if l == r {
            is_lad = true;
        } else {
            let mut k: usize = l;
            while k <= r
                invariant
                    l <= k <= r + 1,
                    !is_lad ==> forall|kk: usize| l <= kk < k ==> !(check_non_decreasing(&arr, l, kk) && check_non_increasing(&arr, kk, r)),
                decreases (r - k + 1),
            {
                if check_non_decreasing(&arr, l, k) && check_non_increasing(&arr, k, r) {
                    is_lad = true;
                    break;
                }
                k = k + 1;
            }
        }
        if is_lad {
            results.push(vec!['Y', 'e', 's']);
        } else {
            results.push(vec!['N', 'o']);
        }
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}