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
/* helper modified by LLM (iteration 5): lemma for the cons-step of sum_mins */
proof fn sum_mins_cons(b: Seq<int>, k: int)
    requires 0 <= k && k < b.len(),
    ensures sum_mins(b, k+1) == b@[k] + sum_mins(b, k),
{
    reveal(sum_mins);
    assert(sum_mins(b, k+1) == b@[k] + sum_mins(b, k));
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, b: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, b@.map(|i: int, x: i8| x as int))
  ensures correct_result(n as int, b@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute result with runtime loop and ghost invariants */
  let ghost bs: Seq<int> = b@.map(|i: int, x: i8| x as int);
  if n == 2 {
    let result: i8 = b[0] + b[0];
    proof {
      let ghost r_int: int = result as int;
      assert(r_int == (b[0] as int) + (b[0] as int));
      assert(r_int == 2 * bs@[0]);
    }
    result
  } else {
    let len_usize: usize = (n as i32 - 2) as usize;
    let mut sum_rt: i64 = 0;
    let mut j: usize = 0;
    let ghost mut gsum: int = 0;
    while j < len_usize
        invariant
            0 <= (j as int),
            (j as int) <= (len_usize as int),
            gsum == sum_rt as int,
        decreases (len_usize as int) - (j as int)
    {
      sum_rt = sum_rt + (b[j] as i64);
      let ghost gj: int = j as int;
      ghost { gsum = gsum + bs@[gj]; }
      j = j + 1;
    }
    let result_rt_i32: i32 = (b[0] as i32) + (b[(n as usize) - 2] as i32) + (sum_rt as i32);
    let result: i8 = result_rt_i32 as i8;
    proof {
      let ghost s: int = gsum;
      let ghost r_int: int = bs@[0] + bs@[(n as int) - 2] + s;
      assert(result as int == r_int);
    }
    result
  }
}
// </vc-code>


}

fn main() {}