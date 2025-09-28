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

spec fn takahashi_cookies_condition(a: int, k: int) -> bool {
    a >= k
}

spec fn aoki_cookies_condition_1(a: int, k: int, b: int) -> bool {
    a >= k
}

spec fn aoki_cookies_condition_2(a: int, k: int, b: int) -> bool {
    !(a >= k) && k - a < b
}

proof fn lemma_expected_takahashi_correct(a: int, b: int, k: int)
    requires valid_input(a, b, k)
    ensures takahashi_cookies_condition(a, k) == (a >= k)
{
}

proof fn lemma_expected_aoki_correct(a: int, b: int, k: int)
    requires valid_input(a, b, k)
    ensures (
        aoki_cookies_condition_1(a, k, b) == (a >= k) &&
        aoki_cookies_condition_2(a, k, b) == (!(a >= k) && k - a < b)
    )
{
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: (i8, i8))
    requires valid_input(a as int, b as int, k as int)
    ensures correct_result(a as int, b as int, k as int, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_expected_takahashi_correct(a as int, b as int, k as int);
        lemma_expected_aoki_correct(a as int, b as int, k as int);
    }
    
    let takahashi: i8;
    let aoki: i8;
    
    if a >= k {
        takahashi = (a - k) as i8;
        aoki = b;
    } else {
        let remaining = (k - a) as i8;
        takahashi = 0;
        aoki = if remaining <= b { b - remaining } else { 0 };
    }
    
    (takahashi, aoki)
}
// </vc-code>


}

fn main() {}