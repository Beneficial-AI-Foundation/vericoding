// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>, k: int) -> bool {
  1 <= arr.len() <= 100 && 1 <= k <= arr.len()
}

spec fn sum_valid_elements(arr: Seq<int>, k: int) -> int {
  sum_valid_elements_up_to(arr, k)
}

spec fn sum_valid_elements_up_to(arr: Seq<int>, n: int) -> int
  decreases n
{
  if n == 0 {
    0int
  } else if 0 <= n-1 < arr.len() {
    let current = if -99 <= arr[n-1] <= 99 { arr[n-1] } else { 0int };
    sum_valid_elements_up_to(arr, n-1) + current
  } else {
    0int
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove ghost code from helpers and fix lemmas */
spec fn sum_valid_elements_up_to_helper(arr: Seq<int>, n: int, accum: int) -> int
    decreases n
{
    if n <= 0 {
        accum
    } else if 0 <= n-1 < arr.len() {
        let current = if -99 <= arr[n-1] <= 99 { arr[n-1] } else { 0int };
        sum_valid_elements_up_to_helper(arr, n-1, accum + current)
    } else {
        accum
    }
}

proof fn sum_valid_elements_lemma(arr: Seq<int>, k: int)
    ensures sum_valid_elements(arr, k) == sum_valid_elements_up_to_helper(arr, k, 0)
    decreases k
{
    if k <= 0 {
        assert(sum_valid_elements(arr, k) == 0);
        assert(sum_valid_elements_up_to_helper(arr, k, 0) == 0);
    } else {
        sum_valid_elements_lemma(arr, k-1);
        if 0 <= k-1 < arr.len() {
            let current = if -99 <= arr[k-1] <= 99 { arr[k-1] } else { 0int };
            assert(sum_valid_elements_up_to_helper(arr, k-1, current) == sum_valid_elements_up_to_helper(arr, k-1, 0) + current);
        }
        assert(sum_valid_elements(arr, k) == sum_valid_elements_up_to_helper(arr, k, 0));
    }
}
// </vc-helpers>

// <vc-spec>
fn add_elements(arr: Vec<i8>, k: i8) -> (result: i8)
  requires valid_input(arr@.map(|i: int, x: i8| x as int), k as int)
  ensures result as int == sum_valid_elements(arr@.map(|i: int, x: i8| x as int), k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix ghost code usage by casting k to usize instead of int */
    let k_usize = k as usize;
    let mut i: usize = 0;
    let mut result: i8 = 0;
    
    while i < k_usize
        invariant i <= k_usize,
            i <= arr.len(),
            result as int == sum_valid_elements_up_to_helper(arr@.map(|idx: int, x: i8| x as int), i as int, 0),
        decreases k_usize - i
    {
        if i < arr.len() {
            let val = arr[i];
            if -99 <= val && val <= 99 {
                let new_val = result as i32 + val as i32;
                assert(-128 <= new_val && new_val <= 127);
                result = new_val as i8;
            }
        }
        i += 1;
    }
    
    proof {
        sum_valid_elements_lemma(arr@.map(|idx: int, x: i8| x as int), k as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}