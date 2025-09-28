// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(p: int) -> bool {
    2 <= p < 2000
}

spec fn count_primitive_roots(p: int) -> int
    recommends valid_input(p)
{
    if p == 2 { 
        1 
    } else { 
        /* Count of integers i where 1 <= i < p-1 and 
           for all j where 2 <= j <= i, not ((p-1) % j == 0 && i % j == 0) */
        Set::new(|i: int| 1 <= i < p-1 && (forall|j: int| 2 <= j <= i ==> !((p-1) % j == 0 && #[trigger] (i % j) == 0))).len() as int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): check absence of common divisors between i and p-1 and relate to spec */
fn no_common_divisor_property(p: i32, i: i32) -> bool
    requires
        2 <= p,
        1 <= i,
        i <= p - 2,
    ensures
        result == (forall|k: int| 2 <= k <= i as int ==> !((p as int - 1) % k == 0 && (i as int) % k == 0)),
{
    let mut j: i32 = 2;
    while j <= i
        invariant
            2 <= j,
            j <= i + 1,
            (forall|k: int| 2 <= k < j as int ==> !((p as int - 1) % k == 0 && (i as int) % k == 0)),
        decreases (i - j + 1) as nat
    {
        if (p - 1) % j == 0 && i % j == 0 {
            return false;
        }
        j = j + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn solve(p: i8) -> (result: i8)
    requires valid_input(p as int)
    ensures 
        result >= 0 &&
        result as int == count_primitive_roots(p as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate candidates and count those satisfying helper property, maintain invariant linking cnt to spec Set */
    let n: i32 = p as i32;
    if n == 2 {
        return 1i8;
    }
    assert(n >= 3);
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n - 1
        invariant
            1 <= i,
            i <= n - 1,
            cnt >= 0,
            (cnt as int) == Set::new(|x: int| 1 <= x < i as int && (forall|j: int| 2 <= j <= x ==> !((n as int - 1) % j == 0 && x % j == 0))).len(),
        decreases (n - 1 - i) as nat
    {
        if no_common_divisor_property(n, i) {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    let result = #[verifier::truncate] cnt as i8;
    result
}
// </vc-code>


}

fn main() {}