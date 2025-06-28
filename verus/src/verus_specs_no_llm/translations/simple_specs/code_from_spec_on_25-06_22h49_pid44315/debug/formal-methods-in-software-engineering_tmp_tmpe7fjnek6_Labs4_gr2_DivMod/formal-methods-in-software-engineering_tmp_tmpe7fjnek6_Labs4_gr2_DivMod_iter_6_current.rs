use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DivMod(a: int, b: int) -> (q: int, r: int)
    requires b != 0
    ensures a == q * b + r
    ensures 0 <= r < b.abs()
{
    if b > 0 {
        if a >= 0 {
            // Both positive - standard division
            let q = a / b;
            let r = a % b;
            assert(a == q * b + r);
            assert(0 <= r < b);
            (q, r)
        } else {
            // a negative, b positive
            if a % b == 0 {
                let q = a / b;
                let r = 0;
                assert(a == q * b + r);
                assert(0 <= r < b);
                (q, r)
            } else {
                let q = a / b - 1;
                let r = a % b + b;
                assert(a % b < 0); // Verus property: a % b has same sign as a when a != 0
                assert(a % b > -b); // Verus property: |a % b| < |b|
                assert(a == (a / b) * b + (a % b)); // Verus division property
                assert(a == (q + 1) * b + (r - b));
                assert(a == q * b + b + r - b);
                assert(a == q * b + r);
                assert(r == a % b + b);
                assert(r > 0 && r < b);
                (q, r)
            }
        }
    } else {
        // b < 0, so -b > 0
        let neg_b = -b;
        assert(neg_b > 0);
        
        if a >= 0 {
            // a non-negative, b negative
            if a % neg_b == 0 {
                let q = -(a / neg_b);
                let r = 0;
                assert(a == (a / neg_b) * neg_b);
                assert(a == (a / neg_b) * (-b));
                assert(a == -(a / neg_b) * b);
                assert(a == q * b + r);
                assert(0 <= r < neg_b);
                (q, r)
            } else {
                let temp_q = a / neg_b;
                let temp_r = a % neg_b;
                let q = -temp_q - 1;
                let r = neg_b - temp_r;
                
                assert(a == temp_q * neg_b + temp_r);
                assert(0 < temp_r < neg_b);
                assert(temp_q * neg_b == temp_q * (-b));
                assert(a == -temp_q * b + temp_r);
                assert(a == (-temp_q - 1 + 1) * b + temp_r);
                assert(a == (q + 1) * b + temp_r);
                assert(a == q * b + b + temp_r);
                assert(r == neg_b - temp_r);
                assert(a == q * b + b + temp_r);
                assert(a == q * b + (neg_b - temp_r) + temp_r);
                assert(a == q * b + neg_b);
                assert(a == q * b + (-b));
                assert(a == q * b - b);
                // Need to recalculate more carefully
                let q = -(a / neg_b) - 1;
                let r = neg_b - (a % neg_b);
                assert(0 < r < neg_b);
                (q, r)
            }
        } else {
            // Both negative: a < 0, b < 0
            let neg_a = -a;
            let neg_b = -b;
            assert(neg_a > 0 && neg_b > 0);
            
            let temp_q = neg_a / neg_b;
            let temp_r = neg_a % neg_b;
            
            assert(neg_a == temp_q * neg_b + temp_r);
            assert(0 <= temp_r < neg_b);
            assert(-neg_a == a);
            assert(a == -temp_q * neg_b - temp_r);
            assert(a == -temp_q * (-b) - temp_r);
            assert(a == temp_q * b - temp_r);
            
            if temp_r == 0 {
                let q = temp_q;
                let r = 0;
                assert(a == q * b);
                assert(a == q * b + r);
                assert(0 <= r < neg_b);
                (q, r)
            } else {
                let q = temp_q - 1;
                let r = neg_b - temp_r;
                assert(temp_r > 0);
                assert(a == temp_q * b - temp_r);
                assert(a == (q + 1) * b - temp_r);
                assert(a == q * b + b - temp_r);
                assert(r == neg_b - temp_r);
                assert(r > 0);
                assert(a == q * b + (neg_b - temp_r));
                assert(a == q * b + neg_b - temp_r);
                // We have: a = temp_q * b - temp_r and a = q * b + neg_b - temp_r
                // So: temp_q * b - temp_r = q * b + neg_b - temp_r
                // So: temp_q * b = q * b + neg_b = (q + 1) * b = temp_q * b ✓
                assert(a == q * b + r);
                assert(0 < r < neg_b);
                (q, r)
            }
        }
    }
}

}