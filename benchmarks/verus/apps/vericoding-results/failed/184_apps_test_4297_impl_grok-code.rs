// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn divisible_by_both(result: int, n: int) -> bool
    recommends n >= 1
{
    result % 2 == 0 && result % n == 0
}

spec fn is_smallest(result: int, n: int) -> bool
    recommends n >= 1
{
    forall|k: int| 1 <= k < result ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n) == 0)
}

spec fn lcm(a: int, b: int) -> int
    recommends a >= 1 && b >= 1
{
    if a % b == 0 {
        a
    } else if b % a == 0 {
        b
    } else {
        a * b
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to fix compilation error in inner proof block */
proof fn divisible_by_both_result(result: int, n: int)
    requires
        n >= 1,
        result == if n % 2 == 0 { n } else { 2 * n },
    ensures
        result % 2 == 0,
        result % n == 0,
{
    if n % 2 == 0 {
        assert(result == n);
        assert(result % n == 0);
        assert(result % 2 == 0);
    } else {
        assert(result == 2 * n);
        assert(result % 2 == 0);
        assert(result % n == 0);
    }
}

proof fn is_smallest_result(result: int, n: int)
    requires
        n >= 1,
        result == if n % 2 == 0 { n } else { 2 * n },
    ensures
        forall|k: int| 1 <= k < result ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n) == 0),
    decreases *;
{
    proof {
        if n % 2 == 0 {
            assert(result == n);
        } else {
            assert(result == 2 * n);
        }
        assert forall|k: int| #[trigger] (k % 2 == 0 && k % n == 0) implies k >= result || k < 1 by {
            // trivial
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        n >= 1,
    ensures 
        result >= 1,
        result as int % 2 == 0 && result as int % n as int == 0,
        forall|k: int| 1 <= k < result as int ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n as int) == 0),
        (n as int % 2 == 0 ==> result as int == n as int) && (n as int % 2 != 0 ==> result as int == n as int * 2),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): updated implementation for lcm with proper arithmetic handling */
    let result = if (n % 2 == 0) { n } else { 2 * n };
    proof {
        divisible_by_both_result(result as int, n as int);
        is_smallest_result(result as int, n as int);
    }
    result
}
// </vc-code>


}

fn main() {}