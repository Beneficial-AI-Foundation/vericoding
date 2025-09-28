// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn common_divisors(a: int, b: int) -> Set<int>
{
  Set::new(|d: int| 1 <= d <= a && a % d == 0 && b % d == 0)
}

spec fn valid_input(a: int, b: int, k: int) -> bool
{
  a > 0 && b > 0 && k >= 1 && common_divisors(a, b).len() >= k
}

spec fn is_kth_largest_common_divisor(a: int, b: int, k: int, result: int) -> bool
{
  valid_input(a, b, k) ==> (
    result > 0 &&
    a % result == 0 && b % result == 0 &&
    common_divisors(a, b).contains(result) &&
    Set::new(|d: int| common_divisors(a, b).contains(d) && d > result).len() == (k - 1)
  )
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: i8)
  requires valid_input(a as int, b as int, k as int)
  ensures is_kth_largest_common_divisor(a as int, b as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed syntax error in invariant by replacing '/' with '||' */
    let min_ab = if a < b { a } else { b };
    let mut d = min_ab;
    let mut count = 0i8;
    let mut result = 0i8;
    while d >= 1
        invariant
            0 <= count <= k,
            result == 0 || count == k,
        decreases d
    {
        proof {
            assert(d as int >= 1);
            assert(d as int <= min_ab as int);
        }
        if a % d == 0 && b % d == 0 {
            count += 1;
            if count == k {
                result = d;
            }
        }
        d -= 1;
    }
    proof {
        assert(valid_input(a as int, b as int, k as int));
        assert(result as int > 0);
    }
    result
}
// </vc-code>


}

fn main() {}