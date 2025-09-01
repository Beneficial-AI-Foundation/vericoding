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
    // The precondition guarantees a * h / 2 <= u64::MAX
    // We need to compute this without overflow
    
    // Key insight: if either a or h is even, we can divide first to avoid overflow
    let result = if h % 2 == 0 {
        // h is even, so h/2 is exact
        let h_half = h / 2;
        
        // We need to prove a * h_half doesn't overflow
        assert(h_half == h / 2);
        assert(a * h_half == a * (h / 2));
        assert(a * (h / 2) == a * h / 2) by {
            // In integer arithmetic, when h is even: (a * (h/2)) == (a * h) / 2
            assert(h % 2 == 0);
            assert(h == 2 * (h / 2));
            assert(a * h == a * (2 * (h / 2)));
            assert(a * h == 2 * (a * (h / 2)));
            assert((a * h) / 2 == (2 * (a * (h / 2))) / 2);
            assert((2 * (a * (h / 2))) / 2 == a * (h / 2));
        }
        assert(a * h_half <= u64::MAX);
        
        a * h_half
    } else if a % 2 == 0 {
        // a is even, so a/2 is exact
        let a_half = a / 2;
        
        // We need to prove a_half * h doesn't overflow
        assert(a_half == a / 2);
        assert(a_half * h == (a / 2) * h);
        assert((a / 2) * h == a * h / 2) by {
            // In integer arithmetic, when a is even: ((a/2) * h) == (a * h) / 2
            assert(a % 2 == 0);
            assert(a == 2 * (a / 2));
            assert(a * h == (2 * (a / 2)) * h);
            assert(a * h == 2 * ((a / 2) * h));
            assert((a * h) / 2 == (2 * ((a / 2) * h)) / 2);
            assert((2 * ((a / 2) * h)) / 2 == (a / 2) * h);
        }
        assert(a_half * h <= u64::MAX);
        
        a_half * h
    } else {
        // Both a and h are odd
        // In this case, we need to compute (a * h) / 2
        // The precondition guarantees the result fits in u64
        
        // First, we need to prove a * h doesn't overflow
        // Since both are odd and a * h / 2 <= u64::MAX, we have a * h <= 2 * u64::MAX + 1
        // But we need to be more careful here
        
        // Actually, we can use a different approach:
        // (a * h) / 2 = ((a-1) * h + h) / 2 = (a-1) * h / 2 + h / 2
        // Since a is odd, a-1 is even, so (a-1)/2 is exact
        
        let a_minus_1_half = (a - 1) / 2;
        
        assert(a >= 1) by { assert(a > 0); }
        assert((a - 1) % 2 == 0) by { assert(a % 2 == 1); }
        assert(a_minus_1_half == (a - 1) / 2);
        assert(h / 2 == (h - 1) / 2) by { 
            assert(h % 2 == 1);
        }
        
        // Now compute: a_minus_1_half * h + h / 2
        assert(a * h / 2 == a_minus_1_half * h + h / 2) by {
            assert(a == (a - 1) + 1);
            assert(a * h == ((a - 1) + 1) * h);
            assert(a * h == (a - 1) * h + h);
            assert(a * h / 2 == ((a - 1) * h + h) / 2);
            assert(((a - 1) * h + h) / 2 == (a - 1) * h / 2 + h / 2);
            assert((a - 1) / 2 * h == (a - 1) * h / 2) by {
                assert((a - 1) % 2 == 0);
                assert((a - 1) == 2 * ((a - 1) / 2));
                assert((a - 1) * h == 2 * ((a - 1) / 2) * h);
                assert((a - 1) * h / 2 == ((a - 1) / 2) * h);
            }
        }
        
        assert(a_minus_1_half * h + h / 2 <= u64::MAX);
        
        a_minus_1_half * h + h / 2
    };
    
    assert(result == a * h / 2);
    result
}
// </vc-code>

fn main() {}
}