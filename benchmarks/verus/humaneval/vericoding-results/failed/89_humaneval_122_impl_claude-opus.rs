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

// </vc-helpers>

// <vc-spec>
fn add_elements(arr: Vec<i8>, k: i8) -> (result: i8)
  requires valid_input(arr@.map(|i: int, x: i8| x as int), k as int)
  ensures result as int == sum_valid_elements(arr@.map(|i: int, x: i8| x as int), k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed loop invariants and added overflow checks */
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    
    // Since k is i8 and we know 1 <= k <= arr.len() <= 100, k as usize is safe
    let k_usize = k as usize;
    
    while i < k_usize
        invariant
            i <= k_usize,
            k_usize <= arr.len(),
            sum as int == sum_valid_elements_up_to(arr@.map(|j: int, x: i8| x as int), i as int),
            valid_input(arr@.map(|j: int, x: i8| x as int), k as int),
        decreases k_usize - i
    {
        let val = arr[i];
        if -99 <= val && val <= 99 {
            // Check for overflow before adding
            if val >= 0 && sum <= 127 - val {
                sum = sum + val;
            } else if val < 0 && sum >= -128 - val {
                sum = sum + val;
            }
        }
        i = i + 1;
    }
    
    sum
}
// </vc-code>


}

fn main() {}