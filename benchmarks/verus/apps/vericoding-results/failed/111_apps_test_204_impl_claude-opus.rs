// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, x: int, y: int) -> bool {
  a > 0 && b > 0 && x > 0 && y > 0
}

spec fn gcd(a: int, b: int) -> int
  recommends a >= 0 && b >= 0
  decreases b when b >= 0
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn min(a: int, b: int) -> int {
  if a <= b { a } else { b }
}

spec fn expected_result(a: int, b: int, x: int, y: int) -> int
  recommends valid_input(a, b, x, y)
{
  let g = gcd(x, y);
  let x_reduced = x / g;
  let y_reduced = y / g;
  min(a / x_reduced, b / y_reduced)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed gcd_divides_both proof with proper division assertions */
proof fn gcd_positive(a: int, b: int)
    requires
        a > 0,
        b >= 0,
    ensures
        gcd(a, b) > 0,
    decreases b
{
    if b == 0 {
        assert(gcd(a, b) == a);
        assert(a > 0);
    } else {
        assert(b > 0);
        assert(0 <= a % b < b);
        gcd_positive(b, a % b);
        assert(gcd(a, b) == gcd(b, a % b));
    }
}

proof fn gcd_divides_both(a: int, b: int)
    requires
        a > 0,
        b >= 0,
    ensures
        b == 0 ==> gcd(a, b) == a,
        b == 0 ==> a % gcd(a, b) == 0,
        b != 0 ==> a % gcd(a, b) == 0,
        b != 0 ==> b % gcd(a, b) == 0,
    decreases b
{
    if b == 0 {
        assert(gcd(a, b) == a);
        assert(a % a == 0);
    } else {
        assert(b > 0);
        let r = a % b;
        let q = a / b;
        assert(0 <= r < b);
        assert(a == q * b + r) by {
            assert(a % b == r);
            assert(a / b == q);
        };
        
        if r == 0 {
            assert(gcd(a, b) == gcd(b, 0));
            assert(gcd(b, 0) == b);
            assert(b % b == 0);
            assert(a % b == 0);
            assert(a == q * b);
            assert(a % b == 0);
        } else {
            gcd_divides_both(b, r);
            let g = gcd(a, b);
            assert(g == gcd(b, r));
            assert(b % g == 0);
            assert(r % g == 0);
            
            let kb = b / g;
            assert(b == kb * g) by {
                assert(b % g == 0);
            };
            let kr = r / g;
            assert(r == kr * g) by {
                assert(r % g == 0);
            };
            assert(a == q * (kb * g) + (kr * g));
            assert(a == (q * kb + kr) * g);
            assert(a % g == 0);
        }
    }
}

fn compute_gcd(a: i8, b: i8) -> (result: i8)
    requires
        a > 0,
        b >= 0,
        a <= 127,
        b <= 127,
    ensures
        result > 0,
        result as int == gcd(a as int, b as int),
    decreases b as int
{
    if b == 0 {
        a
    } else {
        let r = (a % b) as i8;
        compute_gcd(b, r)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8, y: i8) -> (result: i8)
requires 
  valid_input(a as int, b as int, x as int, y as int)
ensures 
  result as int >= 0,
  result as int == expected_result(a as int, b as int, x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed assertions for division by gcd */
    proof {
        gcd_positive(x as int, y as int);
        gcd_divides_both(x as int, y as int);
    }
    
    let g = compute_gcd(x, y);
    
    proof {
        assert(g as int == gcd(x as int, y as int));
        assert(g > 0);
        assert(x as int % g as int == 0);
        assert(y as int % g as int == 0);
    }
    
    let x_reduced = (x / g) as i8;
    let y_reduced = (y / g) as i8;
    
    proof {
        assert(x_reduced as int == x as int / g as int);
        assert(y_reduced as int == y as int / g as int);
        assert(x_reduced as int > 0) by {
            assert(x > 0);
            assert(g > 0);
            assert(x as int % g as int == 0);
            let k = x as int / g as int;
            assert(x as int == k * g as int) by {
                assert(x as int % g as int == 0);
                assert(x as int / g as int == k);
            };
            assert(k > 0) by {
                assert(x as int > 0);
                assert(g as int > 0);
                assert(x as int == k * g as int);
                if k <= 0 {
                    assert(k * g as int <= 0);
                    assert(false);
                }
            };
            assert(x as int / g as int == k);
        };
        assert(y_reduced as int > 0) by {
            assert(y > 0);
            assert(g > 0);
            assert(y as int % g as int == 0);
            let k = y as int / g as int;
            assert(y as int == k * g as int) by {
                assert(y as int % g as int == 0);
                assert(y as int / g as int == k);
            };
            assert(k > 0) by {
                assert(y as int > 0);
                assert(g as int > 0);
                assert(y as int == k * g as int);
                if k <= 0 {
                    assert(k * g as int <= 0);
                    assert(false);
                }
            };
            assert(y as int / g as int == k);
        };
    }
    
    let q1 = (a / x_reduced) as i8;
    let q2 = (b / y_reduced) as i8;
    
    proof {
        assert(q1 as int == a as int / x_reduced as int);
        assert(q2 as int == b as int / y_reduced as int);
        assert(q1 >= 0);
        assert(q2 >= 0);
    }
    
    if q1 <= q2 {
        proof {
            assert(min(q1 as int, q2 as int) == q1 as int);
            assert(expected_result(a as int, b as int, x as int, y as int) == min(a as int / x_reduced as int, b as int / y_reduced as int));
        }
        q1
    } else {
        proof {
            assert(min(q1 as int, q2 as int) == q2 as int);
            assert(expected_result(a as int, b as int, x as int, y as int) == min(a as int / x_reduced as int, b as int / y_reduced as int));
        }
        q2
    }
}
// </vc-code>


}

fn main() {}