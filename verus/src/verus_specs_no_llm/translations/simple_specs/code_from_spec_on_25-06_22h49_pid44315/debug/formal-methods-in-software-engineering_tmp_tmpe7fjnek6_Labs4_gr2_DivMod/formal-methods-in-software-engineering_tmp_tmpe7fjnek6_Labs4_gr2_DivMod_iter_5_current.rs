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
                (q, r)
            }
        }
    } else {
        // b < 0
        if a >= 0 {
            // a non-negative, b negative
            if a % (-b) == 0 {
                let q = -(a / (-b));
                let r = 0;
                (q, r)
            } else {
                let q = -(a / (-b)) - 1;
                let r = (-b) - (a % (-b));
                (q, r)
            }
        } else {
            // Both negative
            let pos_a = -a;
            let pos_b = -b;
            let temp_q = pos_a / pos_b;
            let temp_r = pos_a % pos_b;
            
            if temp_r == 0 {
                let q = temp_q;
                let r = 0;
                (q, r)
            } else {
                let q = temp_q - 1;
                let r = pos_b - temp_r;
                (q, r)
            }
        }
    }
}

}