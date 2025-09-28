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
/* helper modified by LLM (iteration 2): changed index types from int to usize to fix compilation errors */
fn check_non_decreasing(arr: &Vec<i8>, start: usize, end: usize) -> (result: bool)
    requires
        start <= end < arr@.len(),
    ensures
        result == is_non_decreasing(arr@.map(|_i, v| v as int), start as int, end as int),
{
    let mut i = start;
    while i < end
        invariant
            start <= end < arr@.len(),
            start <= i <= end,
            is_non_decreasing(arr@.map(|_i, v| v as int), start as int, i as int),
        decreases end - i,
    {
        if arr[i] > arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

/* helper modified by LLM (iteration 2): changed index types from int to usize to fix compilation errors */
fn check_non_increasing(arr: &Vec<i8>, start: usize, end: usize) -> (result: bool)
    requires
        start <= end < arr@.len(),
    ensures
        result == is_non_increasing(arr@.map(|_i, v| v as int), start as int, end as int),
{
    let mut i = start;
    while i < end
        invariant
            start <= end < arr@.len(),
            start <= i <= end,
            is_non_increasing(arr@.map(|_i, v| v as int), start as int, i as int),
        decreases end - i,
    {
        if arr[i] < arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

/* helper modified by LLM (iteration 2): changed index types from int to usize to fix compilation errors */
fn check_is_ladder(arr: &Vec<i8>, l: usize, r: usize) -> (result: bool)
    requires
        l <= r < arr@.len(),
    ensures
        result == is_ladder(arr@.map(|_i, v| v as int), l as int, r as int),
{
    if l == r {
        return true;
    }

    let mut k = l;
    while k <= r
        invariant
            l <= r < arr@.len(),
            l <= k <= r + 1,
            forall|j: int| l as int <= j < k as int ==> !(
                is_non_decreasing(arr@.map(|_i, v| v as int), l as int, j) &&
                is_non_increasing(arr@.map(|_i, v| v as int), j, r as int)
            ),
        decreases r - k,
    {
        if check_non_decreasing(arr, l, k) && check_non_increasing(arr, k, r) {
            return true;
        }
        k = k + 1;
    }
    return false;
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
{
    /* code modified by LLM (iteration 2): fix compilation error by casting to usize */
    let mut results: Vec<Vec<char>> = Vec::new();
    let mut i: i8 = 0;
    while i < m
        invariant
            arr@.len() == n as int,
            queries@.len() == m as int,
            0 <= i <= m,
            results@.len() == i as int,
            forall|k: int| 0 <= k < m as int ==> 1 <= #[trigger] queries@[k].0 as int <= queries@[k].1 as int <= n as int,
            forall|k: int| 0 <= k < i as int ==> #[trigger] results@[k]@ == seq!['Y', 'e', 's'] || results@[k]@ == seq!['N', 'o'],
            forall|k: int| 0 <= k < i as int ==> 
                (#[trigger] results@[k]@ == seq!['Y', 'e', 's'] <==> is_ladder(arr@.map(|_i, v| v as int), queries@[k].0 as int - 1, queries@[k].1 as int - 1)),
        decreases m - i,
    {
        let l = queries[i as usize].0;
        let r = queries[i as usize].1;

        let l_idx = (l - 1) as usize;
        let r_idx = (r - 1) as usize;

        let is_lad = check_is_ladder(arr, l_idx, r_idx);

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