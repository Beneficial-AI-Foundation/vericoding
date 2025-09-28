use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let m: u32 = if a < b { a } else { b };
    (m)
}
// </vc-code>

fn main() {}

}