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
            // Both positive
            let q = a / b;
            let r = a % b;
            (q, r)
        } else {
            // a negative, b positive
            let q = -((-a - 1) / b + 1);
            let r = a - q * b;
            (q, r)
        }
    } else {
        // b < 0
        if a >= 0 {
            // a non-negative, b negative
            let q = -(a / (-b));
            let r = a - q * b;
            (q, r)
        } else {
            // Both negative
            let q = (-a) / (-b);
            let r = a - q * b;
            (q, r)
        }
    }
}

}

This implementation:


The function implements Euclidean division where the remainder is always non-negative and less than the absolute value of the divisor.