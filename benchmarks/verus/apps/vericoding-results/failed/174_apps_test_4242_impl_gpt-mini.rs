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
spec fn min_int(a: int, b: int) -> int {
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: i8)
  requires valid_input(a as int, b as int, k as int)
  ensures is_kth_largest_common_divisor(a as int, b as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    let aa = a as int;
    let bb = b as int;
    let kk = k as int;
    let m = if aa < bb { aa } else { bb };
    let mut i: int = m;
    let mut cnt: int = 0;
    while i >= 1
        invariant
            cnt >= 0,
            cnt <= kk,
            cnt == Set::new(|d: int| common_divisors(aa, bb).contains(d) && d > i).len(),
        decreases i
    {
        if aa % i == 0 && bb % i == 0 {
            cnt = cnt + 1;
            if cnt == kk {
                return i as i8;
            }
        }
        i = i - 1;
    }
    // valid_input guarantees this point is unreachable; return a default value to satisfy the type checker
    1 as i8
}
// </vc-code>


}

fn main() {}