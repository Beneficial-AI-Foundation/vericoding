use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn mul_u64(a: u64, b: u64) -> int {
    a as int * b as int
}

proof fn mul_div_lemma(a: u64, b: u64)
    requires a > 0, b > 0, mul_u64(a, b) / 2 <= u64::MAX
    ensures (a as int * b as int) / 2 == ((a * b) / 2) as int
{
}

proof fn product_bounds_lemma(a: u64, h: u64)
    requires a > 0, h > 0, a * h / 2 <= u64::MAX
    ensures a as int * h as int <= u64::MAX
{
    assert(a * h / 2 <= u64::MAX);
    assert((a * h) / 2 <= u64::MAX);
    assert(2 * (a * h / 2) <= 2 * u64::MAX);
    assert(a * h - (a * h) % 2 <= 2 * u64::MAX);
    assert(a * h <= 2 * u64::MAX + (a * h) % 2);
    assert((a * h) % 2 <= 1);
    assert(a * h <= 2 * u64::MAX + 1);
    assert(2 * u64::MAX + 1 < (u64::MAX * 2) + 2);
    assert(a * h < (u64::MAX * 2) + 2);
    assert(a as int * h as int == (a * h) as int);
    assert((a * h) as int < (u64::MAX * 2) + 2);
    assert((u64::MAX * 2) + 2 <= u64::MAX + u64::MAX + 2);
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
    let product = a * h;
    product / 2
}
// </vc-code>

}
fn main() {}