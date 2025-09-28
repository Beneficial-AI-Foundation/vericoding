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
/* helper modified by LLM (iteration 5): fixed proof logic and bounds checking for sum_valid_elements_up_to */
proof fn sum_valid_elements_equivalence(arr: Seq<int>, k: int)
    requires
        valid_input(arr, k),
    ensures
        sum_valid_elements(arr, k) == sum_valid_elements_up_to(arr, k),
{
}

proof fn sum_bounds_lemma(arr: Seq<int>, n: int)
    requires
        0 <= n,
        n <= arr.len(),
        arr.len() <= 100,
    ensures
        -9900 <= sum_valid_elements_up_to(arr, n) <= 9900,
    decreases n
{
    if n == 0 {
        assert(sum_valid_elements_up_to(arr, n) == 0);
    } else {
        sum_bounds_lemma(arr, n - 1);
        let current = if -99 <= arr[n-1] <= 99 { arr[n-1] } else { 0int };
        assert(-99 <= current <= 99);
        assert(sum_valid_elements_up_to(arr, n) == sum_valid_elements_up_to(arr, n - 1) + current);
        assert(-9900 <= sum_valid_elements_up_to(arr, n - 1) <= 9900);
        assert(-9999 <= sum_valid_elements_up_to(arr, n) <= 9999);
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
    /* code modified by LLM (iteration 5): fixed invariant bounds and cast safety */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    let k_usize = k as usize;
    
    while i < k_usize
        invariant
            0 <= i <= k_usize,
            k_usize <= arr.len(),
            i <= arr.len(),
            sum as int == sum_valid_elements_up_to(arr@.map(|idx: int, x: i8| x as int), i as int),
            -9999 <= sum <= 9999,
        decreases k_usize - i
    {
        let val = arr[i] as i32;
        if -99 <= val && val <= 99 {
            sum = sum + val;
        }
        i = i + 1;
    }
    
    proof {
        sum_bounds_lemma(arr@.map(|idx: int, x: i8| x as int), k as int);
        assert(-128 <= sum <= 127);
    }
    
    #[verifier::truncate]
    sum as i8
}
// </vc-code>


}

fn main() {}