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
            assert(b.abs() == b);
            assert(0 <= r < b.abs());
            (q, r)
        } else {
            // a negative, b positive
            let div_result = a / b;
            let mod_result = a % b;
            
            if mod_result == 0 {
                let q = div_result;
                let r = 0;
                assert(a == q * b + r);
                assert(0 <= r);
                assert(b.abs() == b);
                assert(r < b.abs());
                (q, r)
            } else {
                // mod_result < 0, so we need to adjust
                let q = div_result - 1;
                let r = mod_result + b;
                assert(a == (div_result * b + mod_result));
                assert(a == (div_result - 1) * b + (mod_result + b));
                assert(a == q * b + r);
                assert(mod_result < 0);
                assert(0 < b);
                assert(0 <= mod_result + b);
                assert(mod_result + b < b);
                assert(0 <= r);
                assert(b.abs() == b);
                assert(r < b.abs());
                (q, r)
            }
        }
    } else {
        // b < 0, so -b > 0
        let neg_b = -b;
        
        if a >= 0 {
            // a non-negative, b negative
            let div_result = a / neg_b;
            let mod_result = a % neg_b;
            
            if mod_result == 0 {
                let q = -div_result;
                let r = 0;
                assert(a == div_result * neg_b);
                assert(a == (-div_result) * b);
                assert(a == q * b + r);
                assert(0 <= r);
                assert(b < 0);
                assert(b.abs() == -b);
                assert(b.abs() == neg_b);
                assert(r < b.abs());
                (q, r)
            } else {
                let q = -div_result - 1;
                let r = neg_b - mod_result;
                assert(a == div_result * neg_b + mod_result);
                assert(a == (-div_result - 1) * b + (neg_b - mod_result));
                assert(a == q * b + r);
                assert(0 < mod_result);
                assert(mod_result < neg_b);
                assert(0 <= neg_b - mod_result);
                assert(neg_b - mod_result < neg_b);
                assert(0 <= r);
                assert(b < 0);
                assert(b.abs() == neg_b);
                assert(r < b.abs());
                (q, r)
            }
        } else {
            // Both negative: a < 0, b < 0
            let neg_a = -a;
            let neg_b = -b;
            let div_result = neg_a / neg_b;
            let mod_result = neg_a % neg_b;
            
            if mod_result == 0 {
                let q = div_result;
                let r = 0;
                assert(neg_a == div_result * neg_b);
                assert(a == div_result * b);
                assert(a == q * b + r);
                assert(0 <= r);
                assert(b < 0);
                assert(b.abs() == neg_b);
                assert(r < b.abs());
                (q, r)
            } else {
                let q = div_result + 1;
                let r = neg_b - mod_result;
                assert(neg_a == div_result * neg_b + mod_result);
                assert(a == -(div_result * neg_b + mod_result));
                assert(a == (div_result + 1) * b + (neg_b - mod_result));
                assert(a == q * b + r);
                assert(0 < mod_result);
                assert(mod_result < neg_b);
                assert(0 <= neg_b - mod_result);
                assert(neg_b - mod_result < neg_b);
                assert(0 <= r);
                assert(b < 0);
                assert(b.abs() == neg_b);
                assert(r < b.abs());
                (q, r)
            }
        }
    }
}

}