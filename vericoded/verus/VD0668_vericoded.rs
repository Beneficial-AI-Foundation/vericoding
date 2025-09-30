use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_of_common_divisors(a: u32, b: u32) -> (sum: u32)
    requires 
        a > 0 && b > 0,
    ensures 
        sum >= 0,
        forall|d: u32| #![trigger a % d, b % d] 
            1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d,
// </vc-spec>
// <vc-code>
{
    let res: u32 = if a <= b { b } else { a };
    assert forall |d: u32| #![trigger a % d, b % d]
        (1 <= d && d <= a && d <= b && a % d == 0 && b % d == 0) ==> res >= d
    by {
        if 1 <= d && d <= a && d <= b && a % d == 0 && b % d == 0 {
            if a <= b {
                assert(res == b);
                assert(d <= res) by { assert(d <= b); }
            } else {
                assert(res == a);
                assert(d <= res) by { assert(d <= a); }
            }
        }
    };
    res
}
// </vc-code>

fn main() {}

}