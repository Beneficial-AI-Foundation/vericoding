use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemmas for arithmetic properties
proof fn lemma_mult_assoc(a: u64, b: u64, c: u64)
    ensures a * (b * c) == (a * b) * c
{}

proof fn lemma_mult_comm(a: u64, b: u64)
    ensures a * b == b * a
{}

proof fn lemma_mult_distrib(a: u64, b: u64, c: u64)
    ensures (a + b) * c == a * c + b * c
{}

proof fn lemma_even_div_exact(n: u64)
    requires n % 2 == 0
    ensures n == 2 * (n / 2)
{}

proof fn lemma_odd_div_floor(n: u64)
    requires n % 2 == 1
    ensures n == 2 * (n / 2) + 1
{}
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
        assert(h % 2 == 0);
        
        // When h is even, h = 2 * (h/2)
        lemma_even_div_exact(h);
        assert(h == 2 * (h / 2));
        assert(h == 2 * h_half);
        
        // Now prove a * h == 2 * (a * h_half)
        assert(a * h == a * (2 * h_half));
        lemma_mult_assoc(a, 2, h_half);
        assert(a * (2 * h_half) == (a * 2) * h_half);
        lemma_mult_comm(a, 2);
        assert((a * 2) * h_half == (2 * a) * h_half);
        lemma_mult_assoc(2, a, h_half);
        assert((2 * a) * h_half == 2 * (a * h_half));
        assert(a * h == 2 * (a * h_half));
        
        assert((a * h) / 2 == a * h_half);
        assert(a * h_half == a * h / 2);
        assert(a * h_half <= u64::MAX);
        
        a * h_half
    } else if a % 2 == 0 {
        // a is even, so a/2 is exact
        let a_half = a / 2;
        
        // We need to prove a_half * h doesn't overflow
        assert(a_half == a / 2);
        assert(a % 2 == 0);
        
        // When a is even, a = 2 * (a/2)
        lemma_even_div_exact(a);
        assert(a == 2 * (a / 2));
        assert(a == 2 * a_half);
        
        // Now prove a * h == 2 * (a_half * h)
        assert(a * h == (2 * a_half) * h);
        lemma_mult_assoc(2, a_half, h);
        assert((2 * a_half) * h == 2 * (a_half * h));
        assert(a * h == 2 * (a_half * h));
        
        assert((a * h) / 2 == a_half * h);
        assert(a_half * h == a * h / 2);
        assert(a_half * h <= u64::MAX);
        
        a_half * h
    } else {
        // Both a and h are odd
        // In this case, we need to compute (a * h) / 2
        // The precondition guarantees the result fits in u64
        
        // We can use: (a * h) / 2 = ((a-1) * h + h) / 2 = (a-1) * h / 2 + h / 2
        // Since a is odd, a-1 is even, so (a-1)/2 is exact
        
        let a_minus_1_half = (a - 1) / 2;
        
        assert(a >= 1) by { assert(a > 0); }
        assert(a % 2 == 1);
        assert((a - 1) % 2 == 0);
        assert(a_minus_1_half == (a - 1) / 2);
        
        // For odd h, h/2 rounds down
        assert(h % 2 == 1);
        let h_half_floor = h / 2;
        
        // Now compute: a_minus_1_half * h + h_half_floor
        // First establish the mathematical relationship
        assert(a == (a - 1) + 1);
        assert(a * h == ((a - 1) + 1) * h);
        lemma_mult_distrib(a - 1, 1, h);
        assert(((a - 1) + 1) * h == (a - 1) * h + 1 * h);
        assert(1 * h == h);
        assert(a * h == (a - 1) * h + h);
        
        // Now for the division by 2
        lemma_even_div_exact(a - 1);
        assert((a - 1) == 2 * ((a - 1) / 2));
        assert((a - 1) == 2 * a_minus_1_half);
        
        assert((a - 1) * h == (2 * a_minus_1_half) * h);
        lemma_mult_assoc(2, a_minus_1_half, h);
        assert((2 * a_minus_1_half) * h == 2 * (a_minus_1_half * h));
        assert((a - 1) * h == 2 * (a_minus_1_half * h));
        
        // Since h is odd, h = 2 * (h/2) + 1
        lemma_odd_div_floor(h);
        assert(h == 2 * (h / 2) + 1);
        assert(h == 2 * h_half_floor + 1);
        
        // So a * h = (a-1) * h + h = 2 * (a_minus_1_half * h) + (2 * h_half_floor + 1)
        //          = 2 * (a_minus_1_half * h + h_half_floor) + 1
        assert(a * h == 2 * (a_minus_1_half * h) + h);
        assert(a * h == 2 * (a_minus_1_half * h) + 2 * h_half_floor + 1);
        assert(a * h == 2 * (a_minus_1_half * h + h_half_floor) + 1);
        
        // Therefore (a * h) / 2 = a_minus_1_half * h + h_half_floor
        assert((a * h) / 2 == a_minus_1_half * h + h_half_floor);
        
        assert(a_minus_1_half * h + h_half_floor <= u64::MAX);
        
        a_minus_1_half * h + h_half_floor
    };
    
    assert(result == a * h / 2);
    result
}
// </vc-code>

fn main() {}
}