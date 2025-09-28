// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a > 0 && b > 0
}

spec fn count_squares(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b when a > 0 && b > 0
{
    if a == 0 || b == 0 {
        0
    } else if a > b {
        if b == 0 { 0 } else {
            a / b + count_squares(a % b, b)
        }
    } else if b > a {
        if a == 0 { 0 } else {
            b / a + count_squares(a, b % a)
        }
    } else {
        1
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Strengthened lemma to properly prove bound and added helper assertions */
proof fn lemma_count_squares_bounded(a: int, b: int)
    requires 
        0 < a <= 127,
        0 < b <= 127,
    ensures count_squares(a, b) <= 127
    decreases a + b
{
    if a == b {
        assert(count_squares(a, b) == 1);
        assert(1 <= 127);
    } else if a > b {
        assert(b > 0);
        let q = a / b;
        let r = a % b;
        assert(0 <= r < b);
        assert(q >= 1);
        assert(a == q * b + r);
        assert(q <= a);
        assert(q <= 127);
        
        if r == 0 {
            assert(count_squares(a, b) == q);
            assert(q <= 127);
        } else {
            assert(0 < r < b);
            lemma_count_squares_bounded(r, b);
            assert(count_squares(r, b) <= 127);
            assert(count_squares(a, b) == q + count_squares(r, b));
            assert(q + count_squares(r, b) <= 127);
        }
    } else {
        assert(b > a);
        assert(a > 0);
        let q = b / a;
        let r = b % a;
        assert(0 <= r < a);
        assert(q >= 1);
        assert(b == q * a + r);
        assert(q <= b);
        assert(q <= 127);
        
        if r == 0 {
            assert(count_squares(a, b) == q);
            assert(q <= 127);
        } else {
            assert(0 < r < a);
            lemma_count_squares_bounded(a, r);
            assert(count_squares(a, r) <= 127);
            assert(count_squares(a, b) == q + count_squares(a, r));
            assert(q + count_squares(a, r) <= 127);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures 
        result >= 0,
        a == b ==> result == 1,
        a > b ==> result >= 1,
        result as int == count_squares(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invariants and proper handling of count_squares spec */
    let mut x = a;
    let mut y = b;
    let mut count: i8 = 0;
    
    proof {
        lemma_count_squares_bounded(a as int, b as int);
        assert(count_squares(a as int, b as int) <= 127);
    }
    
    while x != 0 && y != 0
        invariant
            0 <= x <= 127,
            0 <= y <= 127,
            0 <= count <= 127,
            (x == 0 && y > 0) || (y == 0 && x > 0) || (x > 0 && y > 0) || (x == 0 && y == 0),
            (x == 0 || y == 0) ==> count as int == count_squares(a as int, b as int),
            (x > 0 && y > 0) ==> count as int + count_squares(x as int, y as int) == count_squares(a as int, b as int),
            count_squares(a as int, b as int) <= 127,
        decreases x + y
    {
        if x > y {
            assert(y > 0);
            let quotient = x / y;
            let remainder = x % y;
            
            proof {
                assert(x as int == quotient as int * y as int + remainder as int);
                assert(0 <= remainder as int < y as int);
                if remainder == 0 {
                    assert(count_squares(x as int, y as int) == quotient as int);
                } else {
                    assert(count_squares(x as int, y as int) == quotient as int + count_squares(remainder as int, y as int));
                }
                lemma_count_squares_bounded(x as int, y as int);
            }
            
            count = count + quotient;
            x = remainder;
        } else if y > x {
            assert(x > 0);
            let quotient = y / x;
            let remainder = y % x;
            
            proof {
                assert(y as int == quotient as int * x as int + remainder as int);
                assert(0 <= remainder as int < x as int);
                if remainder == 0 {
                    assert(count_squares(x as int, y as int) == quotient as int);
                } else {
                    assert(count_squares(x as int, y as int) == quotient as int + count_squares(x as int, remainder as int));
                }
                lemma_count_squares_bounded(x as int, y as int);
            }
            
            count = count + quotient;
            y = remainder;
        } else {
            proof {
                assert(x == y);
                assert(x > 0);
                assert(y > 0);
                assert(count_squares(x as int, y as int) == 1);
            }
            count = count + 1;
            x = 0;
            y = 0;
        }
    }
    
    proof {
        assert(x == 0 || y == 0);
        assert(count as int == count_squares(a as int, b as int));
        if a == b {
            assert(count == 1);
        }
        if a > b {
            assert(count >= 1);
        }
    }
    
    count
}
// </vc-code>


}

fn main() {}