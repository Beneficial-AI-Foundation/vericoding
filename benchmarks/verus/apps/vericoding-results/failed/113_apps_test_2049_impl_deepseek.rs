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
fn find_peak_index(arr: &Vec<i8>, l: usize, r: usize) -> (idx: usize)
    requires
        0 <= l <= r < arr@.len(),
    ensures
        l <= idx <= r,
        forall|i: int| l <= i < idx ==> arr@[i] <= arr@[i+1],
        forall|i: int| idx <= i < r ==> arr@[i] >= arr@[i+1],
{
    let mut i = l;
    while i < r
        invariant
            l <= i <= r,
            forall|j: int| l <= j < i ==> arr@[j] <= arr@[j+1],
        decreases
            r - i,
    {
        if arr[i] <= arr[i+1] {
            i += 1;
        } else {
            break;
        }
    }
    i
}

predicate is_non_decreasing_arr(arr: &Vec<i8>, start: usize, end: usize) {
    0 <= start <= end < arr@.len() &&
    forall|i: int| start <= i < end ==> #[trigger] arr@[i] <= arr@[i+1]
}

predicate is_non_increasing_arr(arr: &Vec<i8>, start: usize, end: usize) {
    0 <= start <= end < arr@.len() &&
    forall|i: int| start <= i < end ==> #[trigger] arr@[i] >= arr@[i+1]
}

spec fn seq_is_ladder(arr: Seq<int>, l: int, r: int) -> bool {
    &&& 0 <= l <= r < arr.len()
    &&& if l == r {
        true
    } else {
        exists|k: int| l <= k <= r &&
            is_non_decreasing(arr, l, k) &&
            is_non_increasing(arr, k, r)
    }
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
    let mut results = Vec::with_capacity(m as usize);
    let arr_view = arr@.map(|_i, v| v as int);
    
    for query_idx in 0..m as usize {
        let (l_query, r_query) = queries[query_idx];
        let l = (l_query - 1) as usize;
        let r = (r_query - 1) as usize;
        
        proof {
            if l == r {
                assert(seq_is_ladder(arr_view, l as int, r as int));
            }
        }
        
        let mut result_chars;
        if l == r {
            result_chars = vec!['Y', 'e', 's'];
        } else {
            let peak_idx = find_peak_index(&arr, l, r);
            
            proof {
                if is_non_decreasing_arr(&arr, l, peak_idx) && is_non_increasing_arr(&arr, peak_idx, r) {
                    assert(seq_is_ladder(arr_view, l as int, r as int));
                }
            }
            
            if is_non_decreasing_arr(&arr, l, peak_idx) && is_non_increasing_arr(&arr, peak_idx, r) {
                result_chars = vec!['Y', 'e', 's'];
            } else {
                result_chars = vec!['N', 'o'];
            }
        }
        
        results.push(result_chars);
    }
    
    results
}
// </vc-code>


}

fn main() {}