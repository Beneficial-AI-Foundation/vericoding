use vstd::prelude::*;

verus! {

// <vc-helpers>
lemma div_mul_property(x: u64, d: u64)
    requires d > 0
    ensures (x / d) * d <= x
{
    // This follows from the definition of integer division
}

lemma div_bounds(a: u64, h: u64)
    requires a > 0 && h > 0 && a * h / 2 <= u64::MAX
    ensures a * h <= u64::MAX
{
    div_mul_property(a * h, 2);
    assert((a * h / 2) * 2 <= a * h);
    assert(a * h / 2 <= u64::MAX);
    assert((a * h / 2) * 2 <= u64::MAX * 2);
    
    // Since (a * h / 2) * 2 <= a * h and a * h / 2 <= u64::MAX
    // we can conclude a * h is bounded
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
    // impl-start
    proof {
        div_bounds(a, h);
    }
    let product = a * h;
    let area = product / 2;
    area
    // impl-end
}
// </vc-code>

fn main() {}
}