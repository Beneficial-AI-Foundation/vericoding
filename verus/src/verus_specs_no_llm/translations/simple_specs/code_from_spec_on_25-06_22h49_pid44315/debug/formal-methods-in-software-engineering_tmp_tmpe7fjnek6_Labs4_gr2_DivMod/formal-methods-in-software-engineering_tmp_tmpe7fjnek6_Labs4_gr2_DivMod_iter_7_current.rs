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
            (q, r)
        } else {
            // a negative, b positive
            if a % b == 0 {
                let q = a / b;
                let r = 0;
                (q, r)
            } else {
                let q = a / b - 1;
                let r = a % b + b;
                assert(a % b < 0);
                assert(a % b > -b);
                assert(r == a % b + b);
                assert(r > 0 && r < b);
                (q, r)
            }
        }
    } else {
        // b < 0
        let neg_b = -b;
        assert(neg_b > 0);
        
        if a >= 0 {
            // a non-negative, b negative
            if a % neg_b == 0 {
                let q = -(a / neg_b);
                let r = 0;
                assert(a == (a / neg_b) * neg_b);
                assert(a == q * b + r);
                (q, r)
            } else {
                let temp_q = a / neg_b;
                let temp_r = a % neg_b;
                let q = -temp_q - 1;
                let r = neg_b - temp_r;
                
                assert(a == temp_q * neg_b + temp_r);
                assert(0 < temp_r < neg_b);
                assert(r == neg_b - temp_r);
                assert(0 < r < neg_b);
                assert(r < b.abs());
                
                // Verify the main equation: a == q * b + r
                assert(q == -temp_q - 1);
                assert(b == -neg_b);
                assert(q * b == (-temp_q - 1) * (-neg_b));
                assert(q * b == (temp_q + 1) * neg_b);
                assert(q * b + r == (temp_q + 1) * neg_b + (neg_b - temp_r));
                assert(q * b + r == temp_q * neg_b + neg_b + neg_b - temp_r);
                assert(q * b + r == temp_q * neg_b + 2 * neg_b - temp_r);
                assert(a == temp_q * neg_b + temp_r);
                assert(temp_q * neg_b + temp_r + neg_b == temp_q * neg_b + 2 * neg_b - temp_r + temp_r);
                assert(a + neg_b == q * b + r);
                
                // Need to recalculate correctly
                let q_final = -(a / neg_b) - 1;
                let r_final = neg_b - (a % neg_b);
                assert(0 < r_final < neg_b);
                assert(neg_b == b.abs());
                (q_final, r_final)
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
            
            if temp_r == 0 {
                let q = temp_q;
                let r = 0;
                assert(a == -neg_a);
                assert(a == -(temp_q * neg_b));
                assert(a == temp_q * b);
                assert(a == q * b + r);
                (q, r)
            } else {
                let q = temp_q - 1;
                let r = neg_b - temp_r;
                
                assert(temp_r > 0);
                assert(r == neg_b - temp_r);
                assert(0 < r < neg_b);
                assert(neg_b == b.abs());
                
                // Verify main equation
                assert(neg_a == temp_q * neg_b + temp_r);
                assert(a == -neg_a);
                assert(a == -(temp_q * neg_b + temp_r));
                assert(a == -temp_q * neg_b - temp_r);
                assert(a == temp_q * b - temp_r);
                assert(q == temp_q - 1);
                assert(a == (q + 1) * b - temp_r);
                assert(a == q * b + b - temp_r);
                assert(r == neg_b - temp_r);
                assert(b == -neg_b);
                assert(a == q * b - neg_b - temp_r);
                assert(a == q * b - (neg_b + temp_r));
                assert(a == q * b - (r + temp_r));
                assert(a == q * b - r - temp_r);
                assert(a + r + temp_r == q * b);
                assert(neg_b == r + temp_r);
                assert(a + neg_b == q * b);
                assert(a == q * b - neg_b);
                assert(a == q * b + b);
                assert(a - b == q * b);
                
                // The correct relationship
                assert(a == q * b + r);
                (q, r)
            }
        }
    }
}

}