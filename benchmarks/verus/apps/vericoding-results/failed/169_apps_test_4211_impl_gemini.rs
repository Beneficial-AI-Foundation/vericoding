// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, b: Seq<int>) -> bool {
  n >= 2 && b.len() == n - 1 && forall|i: int| 0 <= i < b.len() ==> b[i] >= 0
}

spec fn sum_mins(b: Seq<int>, len: int) -> int
  decreases len
{
  if len <= 0 {
    0
  } else {
    b[len - 1] + sum_mins(b, len - 1)
  }
}

spec fn correct_result(n: int, b: Seq<int>, result: int) -> bool {
  valid_input(n, b) ==> {
    if n == 2 {
      result == 2 * b[0]
    } else {
      result == b[0] + b[n-2] + sum_mins(b, n-2)
    }
  }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, b: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, b@.map(|i: int, x: i8| x as int))
  ensures correct_result(n as int, b@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing exec `n_int` */
    let ghost b_spec = b@.map(|_idx, x| x as int);

    if n == 2 {
        let val0 = b[0] as i32;
        let result_i32 = 2 * val0;
        let result = result_i32 as i8;
        return result;
    } else {
        let mut sum: i32 = 0;
        let mut i: usize = 0;
        let loop_limit = (n - 2) as usize;

        while i < loop_limit
            invariant
                b@.len() as int == (n as int) - 1,
                0 <= i <= loop_limit,
                sum as int == sum_mins(b_spec, i as int),
            decreases loop_limit - i
        {
            sum = sum + (b[i] as i32);
            i = i + 1;
        }
        
        let val0 = b[0] as i32;
        let val_last = b[(n - 2) as usize] as i32;
        let result_i32 = val0 + val_last + sum;

        let result = result_i32 as i8;
        return result;
    }
}
// </vc-code>


}

fn main() {}