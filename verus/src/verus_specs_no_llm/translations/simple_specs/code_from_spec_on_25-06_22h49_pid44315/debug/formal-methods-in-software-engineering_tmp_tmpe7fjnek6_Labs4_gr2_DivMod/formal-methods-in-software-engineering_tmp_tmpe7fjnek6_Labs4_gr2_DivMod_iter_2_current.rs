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
            // Both positive - use built-in division and modulo
            let q = a / b;
            let r = a % b;
            
            // Verus knows these properties for non-negative division
            assert(a == q * b + r);
            assert(0 <= r < b);
            
            (q, r)
        } else {
            // a negative, b positive
            // We want r >= 0, so we adjust the standard division
            let abs_a = -a;
            let temp_q = abs_a / b;
            let temp_r = abs_a % b;
            
            if temp_r == 0 {
                let q = -temp_q;
                let r = 0;
                
                assert(abs_a == temp_q * b);
                assert(a == -abs_a);
                assert(a == -temp_q * b);
                assert(a == q * b);
                assert(a == q * b + r);
                
                (q, r)
            } else {
                let q = -(temp_q + 1);
                let r = b - temp_r;
                
                assert(abs_a == temp_q * b + temp_r);
                assert(a == -abs_a);
                assert(a == -(temp_q * b + temp_r));
                assert(a == -temp_q * b - temp_r);
                assert(a == -(temp_q + 1) * b + b - temp_r);
                assert(a == q * b + r);
                assert(0 < temp_r < b);
                assert(0 < b - temp_r < b);
                assert(0 <= r < b);
                
                (q, r)
            }
        }
    } else {
        // b < 0
        let abs_b = -b;
        assert(abs_b > 0);
        assert(b.abs() == abs_b);
        
        if a >= 0 {
            // a non-negative, b negative
            let temp_q = a / abs_b;
            let temp_r = a % abs_b;
            
            if temp_r == 0 {
                let q = -temp_q;
                let r = 0;
                
                assert(a == temp_q * abs_b);
                assert(a == temp_q * (-b));
                assert(a == -temp_q * b);
                assert(a == q * b);
                assert(a == q * b + r);
                
                (q, r)
            } else {
                let q = -(temp_q + 1);
                let r = abs_b - temp_r;
                
                assert(a == temp_q * abs_b + temp_r);
                assert(a == temp_q * (-b) + temp_r);
                assert(a == -temp_q * b + temp_r);
                assert(a == -(temp_q + 1) * b + (-b) + temp_r);
                assert(a == q * b + abs_b - temp_r);
                assert(a == q * b + r);
                assert(0 < temp_r < abs_b);
                assert(0 < abs_b - temp_r < abs_b);
                assert(0 <= r < b.abs());
                
                (q, r)
            }
        } else {
            // Both negative
            let abs_a = -a;
            let abs_b = -b;
            let q = abs_a / abs_b;
            let r = abs_a % abs_b;
            
            assert(abs_a == q * abs_b + r);
            assert(a == -abs_a);
            assert(b == -abs_b);
            assert(a == -(q * abs_b + r));
            assert(a == -q * abs_b - r);
            assert(a == q * b - r);
            assert(a == q * b + (-r));
            
            // For the final result, we need r >= 0
            if r == 0 {
                assert(a == q * b);
                assert(0 <= r < b.abs());
                (q, 0)
            } else {
                let final_q = q - 1;
                let final_r = abs_b - r;
                
                assert(a == q * b - r);
                assert(a == (q - 1) * b + b - r);
                assert(a == final_q * b + final_r);
                assert(0 < r < abs_b);
                assert(0 < abs_b - r < abs_b);
                assert(0 <= final_r < b.abs());
                
                (final_q, final_r)
            }
        }
    }
}

}