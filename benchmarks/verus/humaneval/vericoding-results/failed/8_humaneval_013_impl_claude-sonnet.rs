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
/* helper modified by LLM (iteration 5): Fixed type annotations for numeric literals in assertions */
spec fn gcd_spec(a: int, b: int) -> nat
    decreases abs(b)
{
    if a == 0 && b == 0 {
        0
    } else if a == 0 {
        abs(b)
    } else if b == 0 {
        abs(a)
    } else {
        gcd_spec(b, a % b)
    }
}

proof fn lemma_gcd_divides(a: int, b: int)
    ensures
        divides(gcd_spec(a, b) as int, a),
        divides(gcd_spec(a, b) as int, b)
    decreases abs(b)
{
    if a == 0 && b == 0 {
        assert(gcd_spec(a, b) == 0);
        assert(divides(0, 0));
    } else if a == 0 {
        assert(gcd_spec(a, b) == abs(b));
        assert(0int % (abs(b) as int) == 0);
        if b >= 0 {
            assert(b % (abs(b) as int) == 0);
        } else {
            assert(b % (abs(b) as int) == 0);
        }
    } else if b == 0 {
        assert(gcd_spec(a, b) == abs(a));
        if a >= 0 {
            assert(a % (abs(a) as int) == 0);
        } else {
            assert(a % (abs(a) as int) == 0);
        }
        assert(0int % (abs(a) as int) == 0);
    } else {
        lemma_gcd_divides(b, a % b);
        assert(divides(gcd_spec(b, a % b) as int, b));
        assert(divides(gcd_spec(b, a % b) as int, a % b));
        // From divides(g, b) and divides(g, a%b), we get divides(g, a)
        let g = gcd_spec(b, a % b) as int;
        assert(a == (a / b) * b + (a % b));
        assert(divides(g, a));
    }
}

proof fn lemma_gcd_greatest(a: int, b: int, d: int)
    requires
        d > 0,
        divides(d, a),
        divides(d, b)
    ensures
        d <= gcd_spec(a, b) as int
    decreases abs(b)
{
    if a == 0 && b == 0 {
        // This case is impossible since divides(d, 0) && d > 0
        // but we can't assert false directly, need proper handling
        assert(d > 0);
        assert(divides(d, 0));
        assert(0int % d == 0);
    } else if a == 0 {
        assert(gcd_spec(a, b) == abs(b));
        if b >= 0 {
            assert(d <= b);
        } else {
            assert(d <= -b);
        }
    } else if b == 0 {
        assert(gcd_spec(a, b) == abs(a));
        if a >= 0 {
            assert(d <= a);
        } else {
            assert(d <= -a);
        }
    } else {
        // If d divides both a and b, then d divides a%b
        assert(a == (a / b) * b + (a % b));
        assert(divides(d, a % b));
        lemma_gcd_greatest(b, a % b, d);
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
    /* code modified by LLM (iteration 5): Fixed type annotations for numeric literals in assertions */
    if a == 0 && b == 0 {
        proof {
            assert(gcd_spec(a as int, b as int) == 0);
        }
        return 0;
    }
    
    let mut x: i32 = a as i32;
    let mut y: i32 = b as i32;
    
    if x < 0 {
        x = -x;
    }
    if y < 0 {
        y = -y;
    }
    
    while y != 0
        invariant
            x >= 0,
            y >= 0,
            x <= 128,
            y <= 128,
            gcd_spec(x as int, y as int) == gcd_spec(a as int, b as int)
        decreases y
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    
    proof {
        assert(y == 0);
        assert(gcd_spec(x as int, 0int) == abs(x as int));
        assert(x >= 0);
        assert(x == gcd_spec(a as int, b as int));
        lemma_gcd_divides(a as int, b as int);
        
        // Prove all postconditions
        if a != 0 || b != 0 {
            assert(x > 0);
        }
        
        if a == 0 && b == 0 {
            assert(x == 0);
        }
        
        // Greatest property
        assert(forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) ==> {
            lemma_gcd_greatest(a as int, b as int, d);
            d <= x
        });
    }
    
    x as u8
}
// </vc-code>


}

fn main() {}