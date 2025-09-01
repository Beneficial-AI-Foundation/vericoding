use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    // The precondition a * h / 2 <= u64::MAX implies a * h <= 2 * u64::MAX
    // But we need to ensure a * h <= u64::MAX to avoid overflow
    // Since a * h / 2 <= u64::MAX, we have a * h <= 2 * u64::MAX
    // For u64, we need to be more careful about overflow
    
    // We can prove that a * h won't overflow because:
    // From precondition: a * h / 2 <= u64::MAX
    // This means: a * h <= 2 * u64::MAX
    // But for u64 arithmetic, we need a * h <= u64::MAX
    
    assert(a * h / 2 <= u64::MAX) by {
        // This is given by the precondition
    }
    
    // Since division truncates in integer arithmetic, we need to ensure
    // that a * h doesn't overflow
    assert(a as int * h as int / 2 <= u64::MAX as int);
    assert(a as int * h as int <= 2 * u64::MAX as int);
    
    // The precondition guarantees that a * h / 2 fits in u64
    // This means the multiplication a * h might be up to 2 * u64::MAX
    // We need to handle this carefully
    
    let result = if h % 2 == 0 {
        a * (h / 2)
    } else if a % 2 == 0 {
        (a / 2) * h
    } else {
        // Both a and h are odd, so a * h is odd and division by 2 truncates
        assert(a as int * h as int / 2 == (a as int * h as int - 1) / 2);
        (a * h) / 2
    };
    
    assert(result == a * h / 2);
    result
    // impl-end
}
// </vc-code>

fn main() {}
}