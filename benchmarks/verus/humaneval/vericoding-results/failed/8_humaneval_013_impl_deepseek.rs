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
/* helpers modified by LLM (iteration 5): Fix type annotations for literal 1 in decreases clauses */

spec fn gcd_spec(a: int, b: int) -> nat 
    decreases abs(b) + if a % b == b { 1int } else { 0 }, 0
{
    if b == 0 {
        abs(a)
    } else {
        gcd_spec(b, a % b)
    }
}

proof fn gcd_spec_divides_lemma(a: int, b: int)
    requires a != 0 || b != 0
    ensures 
        divides(gcd_spec(a, b) as int, a),
        divides(gcd_spec(a, b) as int, b)
    decreases abs(b) + if a % b == b { 1int } else { 0 }, 0
{
    if b != 0 {
        assert(a % b != b);
        gcd_spec_divides_lemma(b, a % b);
    }
}

proof fn gcd_spec_maximal_lemma(a: int, b: int, d: int)
    requires 
        d > 0,
        divides(d, a),
        divides(d, b)
    ensures d <= gcd_spec(a, b) as int
    decreases abs(b) + if a % b == b { 1int } else { 0 }, 0
{
    if b != 0 {
        assert(a % b != b);
        gcd_spec_maximal_lemma(b, a % b, d);
    }
}

proof fn gcd_spec_zero_case(a: int, b: int)
    ensures gcd_spec(a, b) == 0 <==> (a == 0 && b == 0)
    decreases abs(b) + if a % b == b { 1int } else { 0 }, 0
{
    if b != 0 {
        assert(a % b != b);
        gcd_spec_zero_case(b, a % b);
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
/* code modified by LLM (iteration 5): Fix loop termination condition and add proper handling */
{
    if a == 0 && b == 0 {
        return 0;
    }
    
    let mut x = a as i16;
    let mut y = b as i16;
    
    while y != 0
        invariant
            gcd_spec(x as int, y as int) == gcd_spec(a as int, b as int),
            x >= -128 && x <= 127,
            y >= -128 && y <= 127,
            a != 0 || b != 0 ==> gcd_spec(a as int, b as int) > 0
        decreases abs(y as int)
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    
    let result_abs = if x >= 0 { x as u8 } else { (-x) as u8 };
    proof {
        gcd_spec_divides_lemma(a as int, b as int);
        gcd_spec_zero_case(a as int, b as int);
        assert forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) implies d <= result_abs as int by {
            gcd_spec_maximal_lemma(a as int, b as int, d);
        };
    }
    result_abs
}
// </vc-code>


}

fn main() {}