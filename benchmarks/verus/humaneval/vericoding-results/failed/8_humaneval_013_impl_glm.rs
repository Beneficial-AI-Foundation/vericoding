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
fn gcd_nonnegative(x0: u8, y0: u8) -> (result: u8)
    ensures
        result > 0 <==> (x0 != 0 || y0 != 0),
        result == 0 <==> (x0 == 0 && y0 == 0),
        divides(result as int, x0 as int) && divides(result as int, y0 as int),
        forall|d: int| d > 0 && divides(d, x0 as int) && divides(d, y0 as int) ==> d <= result as int
{
    /* helper modified by LLM (iteration 5): fixed invariant to preserve common divisors and added proof */
    let mut x = x0;
    let mut y = y0;
    if x == 0 && y == 0 {
        return 0;
    }
    while y != 0
        invariant
            x > 0 && y >= 0,
            forall|d: int| divides(d, x as int) && divides(d, y as int) <==> divides(d, x0 as int) && divides(d, y0 as int),
        decreases y
    {
        let temp = y;
        y = x % y;
        x = temp;
        proof {
            assert(forall|d: int| divides(d, temp as int) && divides(d, (x % temp) as int) <==> divides(d, x as int) && divides(d, temp as int));
        }
    }
    x
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
    /* code modified by LLM (iteration 5): fixed absolute value computation and added proof for divisibility */
    if a == 0 && b == 0 {
        return 0;
    }
    let a_abs = if a < 0 { (-a) as u8 } else { a as u8 };
    let b_abs = if b < 0 { (-b) as u8 } else { b as u8 };
    let result = gcd_nonnegative(a_abs, b_abs);
    proof {
        assert(divides(result as int, a as int));
        assert(divides(result as int, b as int));
    }
    result
}
// </vc-code>


}

fn main() {}