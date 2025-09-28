// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, k: int) -> bool {
    a >= 0 && b >= 0 && k >= 0
}

spec fn expected_takahashi_cookies(a: int, b: int, k: int) -> int
    recommends valid_input(a, b, k)
{
    if a >= k { a - k }
    else { 0 }
}

spec fn expected_aoki_cookies(a: int, b: int, k: int) -> int
    recommends valid_input(a, b, k)
{
    if a >= k { b }
    else if k - a < b { b - (k - a) }
    else { 0 }
}

spec fn correct_result(a: int, b: int, k: int, takahashi: int, aoki: int) -> bool
    recommends valid_input(a, b, k)
{
    takahashi == expected_takahashi_cookies(a, b, k) &&
    aoki == expected_aoki_cookies(a, b, k) &&
    takahashi >= 0 && aoki >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): ensure expected cookie counts are nonnegative */
proof fn expected_nonneg(a: int, b: int, k: int)
    requires
        valid_input(a, b, k),
    ensures
        expected_takahashi_cookies(a, b, k) >= 0,
        expected_aoki_cookies(a, b, k) >= 0,
{
    if a >= k {
        assert(expected_takahashi_cookies(a, b, k) == a - k);
        assert(a - k >= 0);
        assert(expected_aoki_cookies(a, b, k) == b);
        assert(b >= 0);
    } else {
        assert(expected_takahashi_cookies(a, b, k) == 0);
        assert(0 >= 0);
        if k - a < b {
            assert(expected_aoki_cookies(a, b, k) == b - (k - a));
            assert(b - (k - a) >= 0);
        } else {
            assert(expected_aoki_cookies(a, b, k) == 0);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: (i8, i8))
    requires valid_input(a as int, b as int, k as int)
    ensures correct_result(a as int, b as int, k as int, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement runtime logic using i8 and verify with ghost proofs */
    if a >= k {
        let tak: i8 = a - k;
        let aok: i8 = b;
        let result = (tak, aok);
        proof {
            let a_int: int = a as int;
            let b_int: int = b as int;
            let k_int: int = k as int;
            assert(expected_takahashi_cookies(a_int, b_int, k_int) == a_int - k_int);
            assert(expected_aoki_cookies(a_int, b_int, k_int) == b_int);
            assert(result.0 as int == expected_takahashi_cookies(a_int, b_int, k_int));
            assert(result.1 as int == expected_aoki_cookies(a_int, b_int, k_int));
        }
        result
    } else {
        let tak: i8 = 0i8;
        let need: i8 = k - a;
        if need < b {
            let aok: i8 = b - need;
            let result = (tak, aok);
            proof {
                let a_int: int = a as int;
                let b_int: int = b as int;
                let k_int: int = k as int;
                assert(expected_takahashi_cookies(a_int, b_int, k_int) == 0);
                assert(expected_aoki_cookies(a_int, b_int, k_int) == b_int - (k_int - a_int));
                assert(result.0 as int == expected_takahashi_cookies(a_int, b_int, k_int));
                assert(result.1 as int == expected_aoki_cookies(a_int, b_int, k_int));
            }
            result
        } else {
            let result = (tak, 0i8);
            proof {
                let a_int: int = a as int;
                let b_int: int = b as int;
                let k_int: int = k as int;
                assert(expected_takahashi_cookies(a_int, b_int, k_int) == 0);
                assert(expected_aoki_cookies(a_int, b_int, k_int) == 0);
                assert(result.0 as int == expected_takahashi_cookies(a_int, b_int, k_int));
                assert(result.1 as int == expected_aoki_cookies(a_int, b_int, k_int));
            }
            result
        }
    }
}

// </vc-code>


}

fn main() {}