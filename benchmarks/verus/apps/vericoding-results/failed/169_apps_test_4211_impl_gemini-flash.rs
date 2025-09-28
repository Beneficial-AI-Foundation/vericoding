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
/* code modified by LLM (iteration 4): Fix compilation errors by removing `as int` from indexing and ensure `total_sum` accumulates `i8` values correctly. */
{
    let ghost n_int = n as int;
    let ghost b_seq = b@.map(|i: int, x: i8| x as int);

    if n == 2 {
        return (2 * b[0]);
    } else {
        let mut total_sum: i8 = 0;
        let mut i: i8 = 0;

        while i < n - 2
            invariant
                0 <= i,
                i <= n - 2,
                total_sum as int == sum_mins(b_seq, i as int),
        {
            total_sum = total_sum + b[i as usize];
            i = i + 1;
        }

        return (b[0] + b[(n - 2) as usize] + total_sum);
    }
}
// </vc-code>


}

fn main() {}