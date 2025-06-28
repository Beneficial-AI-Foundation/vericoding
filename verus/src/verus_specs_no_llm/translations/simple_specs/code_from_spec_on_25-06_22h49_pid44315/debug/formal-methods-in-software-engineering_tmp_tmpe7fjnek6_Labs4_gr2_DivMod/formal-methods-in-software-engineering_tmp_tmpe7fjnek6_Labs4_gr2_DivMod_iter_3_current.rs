use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function for division
spec fn div_int(a: int, b: int) -> int
    recommends b != 0
{
    if a >= 0 && b > 0 {
        a / b
    } else if a < 0 && b > 0 {
        if a % b == 0 {
            a / b
        } else {
            a / b - 1
        }
    } else if a >= 0 && b < 0 {
        if a % (-b) == 0 {
            -(a / (-b))
        } else {
            -(a / (-b)) - 1
        }
    } else {
        (-a) / (-b)
    }
}

// Helper spec function for modulo
spec fn mod_int(a: int, b: int) -> int 
    recommends b != 0
{
    a - div_int(a, b) * b
}

fn DivMod(a: int, b: int) -> (q: int, r: int)
    requires b != 0
    ensures a == q * b + r
    ensures 0 <= r < b.abs()
{
    if b > 0 {
        if a >= 0 {
            // Both positive
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
                let r = a - q * b;
                assert(r == a - (a / b - 1) * b);
                assert(r == a - a / b * b + b);
                assert(r == a % b + b);
                assert(0 <= r < b);
                (q, r)
            }
        }
    } else {
        // b < 0
        let abs_b = -b;
        if a >= 0 {
            // a non-negative, b negative
            if a % abs_b == 0 {
                let q = -(a / abs_b);
                let r = 0;
                (q, r)
            } else {
                let q = -(a / abs_b) - 1;
                let r = a - q * b;
                assert(r == a - (-(a / abs_b) - 1) * b);
                assert(r == a - (-(a / abs_b) - 1) * (-abs_b));
                assert(r == a - (-a / abs_b - 1) * abs_b);
                assert(r == a - (-a / abs_b) * abs_b - abs_b);
                assert(r == a - (-(a / abs_b * abs_b)) - abs_b);
                assert(r == a + a / abs_b * abs_b - abs_b);
                assert(r == a % abs_b + abs_b - abs_b) by {
                    assert(a == (a / abs_b) * abs_b + a % abs_b);
                };
                assert(r == a % abs_b);
                // Need to adjust r to be positive
                let final_r = abs_b - (a % abs_b);
                let final_q = q - 1;
                assert(0 <= final_r < abs_b);
                assert(abs_b == b.abs());
                (final_q, final_r)
            }
        } else {
            // Both negative
            let abs_a = -a;
            let abs_b = -b;
            let q = abs_a / abs_b;
            let temp_r = abs_a % abs_b;
            
            if temp_r == 0 {
                let r = 0;
                assert(abs_a == q * abs_b);
                assert(a == -abs_a);
                assert(a == -(q * abs_b));
                assert(a == q * (-abs_b));
                assert(a == q * b);
                (q, r)
            } else {
                let final_q = q - 1;
                let final_r = abs_b - temp_r;
                
                assert(abs_a == q * abs_b + temp_r);
                assert(a == -abs_a);
                assert(a == -(q * abs_b + temp_r));
                assert(a == -q * abs_b - temp_r);
                assert(a == q * (-abs_b) - temp_r);
                assert(a == q * b - temp_r);
                assert(a == (q - 1) * b + b - temp_r);
                assert(a == final_q * b + final_r);
                assert(0 < temp_r < abs_b);
                assert(0 < abs_b - temp_r < abs_b);
                assert(0 <= final_r < b.abs());
                
                (final_q, final_r)
            }
        }
    }
}

}