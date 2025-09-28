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
/* helper modified by LLM (iteration 5): fixed type mismatch in sum_mins call */
proof fn bound_result(n: int, b: Seq<int>) -> (res: int)
    requires valid_input(n, b)
    ensures res == b[0] + sum_mins(b, b.len() as int) && res <= 127 * n,
{
    let sum = sum_mins(b, b.len() as int);
    let res = b[0] + sum;
    assert(sum <= (n - 1) * 127);
    assert(res <= 127 + (n - 1) * 127);
    assert(res <= n * 127);
    res
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, b: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, b@.map(|i: int, x: i8| x as int))
  ensures correct_result(n as int, b@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch in sum_mins call */
    let mut total: i16 = 0;
    let mut i: usize = 0;
    while i < b.len()
        invariant
            0 <= i <= b.len(),
            total as int == sum_mins(b@.map(|i: int, x: i8| x as int), i as int),
        decreases (b.len() - i) as nat,
    {
        total += b[i] as i16;
        i += 1;
    }
    let res = total + (b[0] as i16);
    proof {
        let n_val = n as int;
        let b_seq = b@.map(|i: int, x: i8| x as int);
        let expected = b_seq[0] + sum_mins(b_seq, b_seq.len() as int);
        assert(res as int == expected);
        let _ = bound_result(n_val, b_seq);
        assert(expected >= -128 && expected <= 127);
    }
    res as i8
}
// </vc-code>


}

fn main() {}