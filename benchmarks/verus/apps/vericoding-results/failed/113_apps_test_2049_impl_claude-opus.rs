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
/* helper modified by LLM (iteration 5): Added trigger annotations to quantifier in check_is_ladder loop invariant */
proof fn lemma_single_element_is_ladder(arr: Seq<int>, i: int)
    requires
        0 <= i < arr.len(),
    ensures
        is_ladder(arr, i, i),
{
    assert(is_non_decreasing(arr, i, i));
    assert(is_non_increasing(arr, i, i));
}

proof fn lemma_check_ladder_properties(arr: Seq<int>, l: int, r: int, k: int)
    requires
        0 <= l <= r < arr.len(),
        l <= k <= r,
        is_non_decreasing(arr, l, k),
        is_non_increasing(arr, k, r),
    ensures
        is_ladder(arr, l, r),
{
}

fn check_non_decreasing(arr: &Vec<i8>, start: usize, end: usize) -> (result: bool)
    requires
        start <= end < arr@.len(),
    ensures
        result <==> is_non_decreasing(arr@.map(|_i, v| v as int), start as int, end as int),
{
    if start == end {
        return true;
    }
    
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            forall|j: int| start as int <= j < i as int ==> #[trigger] (arr@[j] as int) <= arr@[j+1] as int,
        decreases end - i
    {
        if arr[i] > arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

fn check_non_increasing(arr: &Vec<i8>, start: usize, end: usize) -> (result: bool)
    requires
        start <= end < arr@.len(),
    ensures
        result <==> is_non_increasing(arr@.map(|_i, v| v as int), start as int, end as int),
{
    if start == end {
        return true;
    }
    
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            forall|j: int| start as int <= j < i as int ==> #[trigger] (arr@[j] as int) >= arr@[j+1] as int,
        decreases end - i
    {
        if arr[i] < arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

fn check_is_ladder(arr: &Vec<i8>, l: usize, r: usize) -> (result: bool)
    requires
        l <= r < arr@.len(),
    ensures
        result <==> is_ladder(arr@.map(|_i, v| v as int), l as int, r as int),
{
    if l == r {
        proof {
            lemma_single_element_is_ladder(arr@.map(|_i, v| v as int), l as int);
        }
        return true;
    }
    
    let mut k = l;
    while k <= r
        invariant
            l <= k <= r + 1,
            forall|j: int| l as int <= j < k as int ==> 
                !(#[trigger] is_non_decreasing(arr@.map(|_i, v| v as int), l as int, j) && 
                  is_non_increasing(arr@.map(|_i, v| v as int), j, r as int)),
        decreases r + 1 - k
    {
        let is_non_dec = check_non_decreasing(arr, l, k);
        let is_non_inc = check_non_increasing(arr, k, r);
        
        if is_non_dec && is_non_inc {
            proof {
                lemma_check_ladder_properties(arr@.map(|_i, v| v as int), l as int, r as int, k as int);
            }
            return true;
        }
        k = k + 1;
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
    /* code modified by LLM (iteration 5): No changes needed to main code */
    let mut results: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    
    while i < m
        invariant
            0 <= i <= m,
            results@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] results@[j]@ == seq!['Y', 'e', 's'] || results@[j]@ == seq!['N', 'o'],
            forall|j: int| 0 <= j < i as int ==> 
                (#[trigger] results@[j]@ == seq!['Y', 'e', 's'] <==> is_ladder(arr@.map(|_k, v| v as int), queries@[j].0 as int - 1, queries@[j].1 as int - 1)),
        decreases m - i
    {
        let (l, r) = queries[i as usize];
        let is_ladder_result = check_is_ladder(&arr, (l - 1) as usize, (r - 1) as usize);
        
        let answer = if is_ladder_result {
            let mut yes = Vec::new();
            yes.push('Y');
            yes.push('e');
            yes.push('s');
            yes
        } else {
            let mut no = Vec::new();
            no.push('N');
            no.push('o');
            no
        };
        
        results.push(answer);
        i = i + 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}