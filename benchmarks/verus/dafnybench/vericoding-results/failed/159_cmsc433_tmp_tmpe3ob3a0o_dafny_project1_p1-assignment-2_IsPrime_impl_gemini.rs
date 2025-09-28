// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, helper is correct. */
spec fn no_divisors_in_range(m: i32, start: int, end: int) -> bool {
    forall|j: int| start <= j < end ==> #[trigger] (m % (j as i32)) != 0
}
// </vc-helpers>

// <vc-spec>
fn is_prime(m: i32) -> (result: bool)
    requires m > 0
    ensures result <==> (m > 1 && forall|j: int| 2 <= j < m ==> #[trigger] (m % j as i32) != 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used a proof block to show existence of a divisor, fixing compilation error */
    if m <= 1 {
        return false;
    }

    let mut i: i32 = 2;
    while i < m
        invariant
            m > 1,
            2 <= i,
            i <= m,
            no_divisors_in_range(m, 2, i as int),
        decreases m - i
    {
        if m % i == 0 {
            proof {
                assert(exists|j: int| 2 <= j < (m as int) && (m % (j as i32)) == 0);
            }
            return false;
        }
        i = i + 1;
    }

    return true;
}
// </vc-code>

}
fn main() {}