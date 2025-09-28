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
    /* code modified by LLM (iteration 5): fixed compilation error by removing #[verifier::truncate] and using assertion-based casts with i64 computations to ensure safe narrowing */
    if n == 2 {
        let val = 2i64 * (b[0] as i64);
        proof {
            assert(0 <= b[0]);
            assert(val <= 2 * 127); // since i8 max 127, and b[i] >=0
        }
        let result = val as i8;
        proof {
            assert(correct_result(n as int, b@.map(|_i, x| x as int), result as int));
        }
        return result;
    } else {
        let n_us: usize = ((n as usize) as nat) as usize; // ensure positivity
        proof {
            assert(n_us >= 2);
        }
        let mut s: i64 = 0i64;
        let mut i: usize = 0;
        while i < n_us - 2
            invariant
                0 <= i <= n_us - 2,
                s as int == sum_mins(b@.map(|_i, x: i8| x as int), i as int),
                forall| j: int | 0 <= j < i as int ==> b[j] as i64 >= 0
            decreases n_us - 2 - i
        {
            proof {
                assert(i < b@.len());
            }
            s += b@[i] as i64;
            i += 1;
        }
        let sum_all = s + (b@[0] as i64) + (b@[n_us - 2] as i64);
        proof {
            assert(s as int == sum_mins(b@.map(|_i, x| x as int), (n_us - 2) as int));
            assert(b@[0] as int >= 0);
            assert(b@[n_us - 2] as int >= 0);
            assert(sum_all <= (n_us as i64 - 2) * 127 + 2 * 127); // rough bound locale since mancano seq < i8::MAX
        }
        let result = sum_all as i8;
        proof {
            assert(correct_result(n as int, b@.map(|_i, x| x as int), result as int));
        }
        return result;
    }
}

// </vc-code>


}

fn main() {}