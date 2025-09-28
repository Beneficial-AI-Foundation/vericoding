// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> nat {
    if x >= 0 { x as nat } else { (-x) as nat }
}

spec fn divides(d: int, n: int) -> bool {
    if d == 0 { n == 0 } else { n % d == 0 }
}
// </vc-preamble>

// <vc-helpers>
spec fn gcd(a: int, b: int) -> nat decreases (abs(a) + abs(b) as nat) {
    if a == 0 && b == 0 {
        0
    } else {
        if b == 0 {
            abs(a)
        } else {
            gcd(b, a % b)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn greatest_common_divisor(a: i8, b: i8) -> (result: u8)
    ensures 
        result > 0 <==> (a != 0 || b != 0),
        result == 0 <==> (a == 0 && b == 0),
        divides(result as int, a as int) && divides(result as int, b as int),
        forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) ==> d <= result as int
// </vc-spec>
// <vc-code>
{
    if a == 0 && b == 0 {
        return 0;
    }
    let mut x = if a < 0 { (-(a as i32)) as u8 } else { a as u8 };
    let mut y = if b < 0 { (-(b as i32)) as u8 } else { b as u8 };
    while y != 0
        invariant
            gcd(x as int, y as int) == gcd(a as int, b as int),
            x as int > 0 || y as int > 0
        decreases y as nat
    {
        let temp = x;
        x = y;
        y = temp % x;
    }
    x
}
// </vc-code>


}

fn main() {}