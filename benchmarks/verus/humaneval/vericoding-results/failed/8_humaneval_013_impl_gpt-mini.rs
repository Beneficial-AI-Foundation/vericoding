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
/* helper modified by LLM (iteration 5): absolute value for i8 */
spec fn abs_i8(x: i8) -> i8 { if x >= 0 { x } else { 0i8 - x } }
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
    /* code modified by LLM (iteration 5): gcd by brute-force using i8 primitives */
    let ax: i8 = abs_i8(a);
    let ay: i8 = abs_i8(b);
    let m: i8 = if ax >= ay { ax } else { ay };
    let mut i: i8 = 1i8;
    let mut g: i8 = 0i8;
    while i <= m
        invariant
            1i8 <= i,
            i <= m + 1i8,
            0i8 <= g,
            g <= m,
            (g == 0i8 || (divides(g as int, a as int) && divides(g as int, b as int))),
            forall|d: int| d > 0 && d < i as int && divides(d, a as int) && divides(d, b as int) ==> d <= g as int,
        decreases
            m + 1i8 - i
    {
        if ax % i == 0i8 && ay % i == 0i8 {
            g = i;
        }
        i = i + 1i8;
    }
    let result: u8 = g as u8;
    proof {
        assert((a == 0i8 && b == 0i8) ==> (ax == 0i8 && ay == 0i8));
        assert((ax == 0i8 && ay == 0i8) ==> m == 0i8);
        assert(g <= m);
        assert((a == 0i8 && b == 0i8) ==> g == 0i8);
        assert((a == 0i8 && b == 0i8) ==> result == 0u8);
        assert((a != 0i8 || b != 0i8) ==> m >= 1i8);
        assert(i <= m + 1i8);
        assert(i > m);
        assert(i == m + 1i8);
        assert(divides(1 as int, a as int) && divides(1 as int, b as int));
        assert(m >= 1i8 ==> 1i8 < i);
        assert(m >= 1i8 ==> 1i8 <= g);
        assert((a != 0i8 || b != 0i8) ==> result > 0u8);
        assert((g == 0i8) || (divides(g as int, a as int) && divides(g as int, b as int)));
        if result > 0u8 {
            assert(divides(g as int, a as int) && divides(g as int, b as int));
        } else {
            assert(a == 0i8 && b == 0i8);
        }
        assert(forall|d: int| d > 0 && d < i as int && divides(d, a as int) && divides(d, b as int) ==> d <= g as int);
        assert(i == m + 1i8);
        assert(forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) ==> d <= result as int);
    }
    result
}
// </vc-code>


}

fn main() {}