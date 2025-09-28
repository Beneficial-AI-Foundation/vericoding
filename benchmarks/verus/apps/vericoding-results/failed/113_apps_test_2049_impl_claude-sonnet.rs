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
/* helper modified by LLM (iteration 5): fixed bounds checking and loop termination for all helper functions */
proof fn lemma_ladder_exists_pivot(arr: Seq<int>, l: int, r: int)
    requires
        0 <= l <= r < arr.len(),
        is_ladder(arr, l, r),
    ensures
        exists|k: int| l <= k <= r && is_non_decreasing(arr, l, k) && is_non_increasing(arr, k, r),
{
    if l == r {
        assert(is_non_decreasing(arr, l, l));
        assert(is_non_increasing(arr, l, l));
    }
}

fn check_non_decreasing(arr: &Vec<i8>, start: usize, end: usize) -> (result: bool)
    requires
        start <= end < arr@.len(),
    ensures
        result == is_non_decreasing(arr@.map(|_i, v| v as int), start as int, end as int),
{
    if start == end {
        return true;
    }
    
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            i < arr@.len(),
            forall|j: int| start as int <= j < i as int ==> j + 1 < arr@.len(),
            forall|j: int| start as int <= j < i as int ==> #[trigger] arr@[j] as int <= arr@[j+1] as int,
        decreases end - i
    {
        assert(i < arr@.len());
        assert(i + 1 <= end);
        assert(i + 1 < arr@.len());
        
        if arr[i] > arr[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}

fn check_non_increasing(arr: &Vec<i8>, start: usize, end: usize) -> (result: bool)
    requires
        start <= end < arr@.len(),
    ensures
        result == is_non_increasing(arr@.map(|_i, v| v as int), start as int, end as int),
{
    if start == end {
        return true;
    }
    
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            i < arr@.len(),
            forall|j: int| start as int <= j < i as int ==> j + 1 < arr@.len(),
            forall|j: int| start as int <= j < i as int ==> #[trigger] arr@[j] as int >= arr@[j+1] as int,
        decreases end - i
    {
        assert(i < arr@.len());
        assert(i + 1 <= end);
        assert(i + 1 < arr@.len());
        
        if arr[i] < arr[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}

fn check_ladder(arr: &Vec<i8>, l: usize, r: usize) -> (result: bool)
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
            l <= k <= r + 1,
            k <= arr@.len(),
        decreases r + 1 - k
    {
        assert(k <= r);
        assert(r < arr@.len());
        assert(k < arr@.len());
        
        let non_dec = check_non_decreasing(arr, l, k);
        let non_inc = check_non_increasing(arr, k, r);
        
        if non_dec && non_inc {
            return true;
        }
        k += 1;
    }
    false
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
    /* code modified by LLM (iteration 5): fixed arithmetic operations and bounds checking */
    let mut results: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    
    while i < queries.len()
        invariant
            i <= queries@.len(),
            results@.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] results@[j]@ == seq!['Y', 'e', 's'] || results@[j]@ == seq!['N', 'o'],
            forall|j: int| 0 <= j < i as int ==> 
                (#[trigger] results@[j]@ == seq!['Y', 'e', 's'] <==> is_ladder(arr@.map(|_k, v| v as int), queries@[j].0 as int - 1, queries@[j].1 as int - 1)),
        decreases queries@.len() - i
    {
        let (l, r) = queries[i];
        
        assert(l >= 1);
        assert(r >= l);
        assert(r <= arr@.len() as i8);
        
        let l_idx = (l - 1) as usize;
        let r_idx = (r - 1) as usize;
        
        assert(l_idx <= r_idx);
        assert(r_idx < arr@.len());
        
        let is_ladder_result = check_ladder(&arr, l_idx, r_idx);
        
        if is_ladder_result {
            results.push(vec!['Y', 'e', 's']);
        } else {
            results.push(vec!['N', 'o']);
        }
        
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}