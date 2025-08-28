use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn mul_div_2(a: u64, b: u64) -> u64 {
    (a as nat * b as nat / 2) as u64
}

proof fn arithmetic_properties(a: u64, h: u64)
    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX,
    ensures
        (a as nat * h as nat / 2) as u64 == a * h / 2,
{
    assert(a as nat <= u64::MAX as nat);
    assert(h as nat <= u64::MAX as nat);
    assert(a as nat * h as nat / 2 <= u64::MAX as nat);
}
// </vc-helpers>

// <vc-spec>
fn triangle_area(a: u64, h: u64) -> (area: u64)
    // pre-conditions-start
    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX
        ,
    // pre-conditions-end
    // post-conditions-start
    ensures
        area == a * h / 2,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    proof {
        arithmetic_properties(a, h);
    }
    a * h / 2
}
// </vc-code>

}
fn main() {}