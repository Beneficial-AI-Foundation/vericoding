// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}
// </vc-preamble>

// <vc-helpers>
fn next_multiple(n: int, k: int) -> (r: int)
    requires
        n >= 1,
        k > 0,
    ensures
        is_correct_result(n, k, r),
{
    let rem = n % k;
    let delta = if rem == 0 { k } else { k - rem };
    let r = n + delta;
    proof {
        let q = n / k;
        assert(n == q * k + rem);
        assert(r > n);
        assert(q * k + rem + delta == (q + 1) * k);
        assert(r % k == 0);

        assert(forall |x: int| n < x && x < r ==> x % k != 0) by {
            let d = x - n;
            assert(0 < d && d < delta);
            if rem == 0 {
                assert(1 <= d && d < k);
                assert(x == q * k + d);
                assert(x % k == d % k);
                assert(d % k == d);
                assert(d != 0);
            } else {
                assert(1 <= d && d < k - rem);
                assert(rem + d < k);
                assert(rem + d >= 1);
                assert(x == q * k + rem + d);
                assert(x % k == (rem + d) % k);
                assert((rem + d) % k == rem + d);
                assert(rem + d != 0);
            }
        }
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    let n_int: int = n as int;
    let k_int: int = k as int;
    let r: int = next_multiple(n_int, k_int);
    let result: i8 = r as i8;
    result
}
// </vc-code>


}

fn main() {}