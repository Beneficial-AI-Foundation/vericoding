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
  /* code modified by LLM (iteration 2): fixed invariant block syntax */
  let mut total: int = 0;
  let mut i: int = 0;
  while i < k as int
      invariant
          0 <= i <= k as int,
          total == sum_valid_elements_up_to(arr@.map(|j: int, x: i8| x as int), i),
      decreases (k as int) - i
  {
      let x = arr[i as usize];
      if -99 <= x && x <= 99 {
          total += x as int;
      }
      i += 1;
  }
  total as i8
}
// </vc-code>


}

fn main() {}