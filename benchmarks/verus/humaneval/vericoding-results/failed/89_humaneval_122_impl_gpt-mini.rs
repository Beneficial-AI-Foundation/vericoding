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
/* helper modified by LLM (iteration 3): convert Vec<i8> to Seq<int> */
spec fn vec_i8_to_seq(v: Vec<i8>) -> Seq<int> {
  v@.map(|i: int, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn add_elements(arr: Vec<i8>, k: i8) -> (result: i8)
  requires valid_input(arr@.map(|i: int, x: i8| x as int), k as int)
  ensures result as int == sum_valid_elements(arr@.map(|i: int, x: i8| x as int), k as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implement loop using ghost variables with correct declaration */
  let mut i: usize = 0;
  let mut acc_val: i64 = 0;
  ghost let mut i_g: nat = 0;
  ghost let mut acc_g: int = 0;
  while i < (k as usize)
      invariant
          0 <= i_g <= k as int,
          acc_g == sum_valid_elements_up_to(arr@.map(|i: int, x: i8| x as int), i_g),
          acc_val as int == acc_g,
      decreases k as int - i_g
  {
      let ai: i8 = arr.get(i);
      if -99 <= (ai as i32) && (ai as i32) <= 99 {
          acc_val = acc_val + (ai as i64);
      }
      i = i + 1;

      proof {
          let ai_int: int = ai as int;
          if -99 <= ai_int && ai_int <= 99 {
              acc_g = acc_g + ai_int;
          }
          i_g = i_g + 1;
          assert(acc_g == sum_valid_elements_up_to(arr@.map(|i: int, x: i8| x as int), i_g));
      }
  }

  proof {
      assert(i_g == k as int);
      assert(acc_val as int == acc_g);
  }

  let result: i8 = acc_val as i8;
  result
}
// </vc-code>


}

fn main() {}