// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_rectangle_parts(a: int, b: int, n: int) -> bool {
    a > 0 && b > 0 && a != b && 2 * a + 2 * b == n
}

spec fn count_valid_rectangles(n: int) -> int
    recommends n > 0
{
    if n % 2 == 1 { 0 }
    else if n % 4 == 2 { n / 4 }
    else { n / 4 - 1 }
}

spec fn valid_input(n: int) -> bool {
    n > 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_even_number_alternatives(n: int)
    requires
        n > 0,
        n % 2 == 0,
    ensures
        n % 4 == 2 || n % 4 == 0,
    decreases n
{
    /* helper modified by LLM (iteration 3): Added proper modulo lemma */
    let remainder = n % 4;
    assert(remainder == 0 || remainder == 1 || remainder == 2 || remainder == 3) by {
        assert(0 <= remainder && remainder < 4);
    };
    assert(remainder % 2 == 0) by {
        assert(n % 2 == 0);
        assert(remainder == n % 4);
        assert(n % 4 == remainder);
        assert(n % 2 == remainder % 2);
    };
    assert(remainder == 0 || remainder == 2) by {
        assert(remainder >= 0 && remainder < 4);
        assert(remainder % 2 == 0);
    };
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == count_valid_rectangles(n as int) &&
        (n as int % 2 == 1 ==> result as int == 0) &&
        (n as int % 2 == 0 && n as int % 4 == 2 ==> result as int == n as int / 4) &&
        (n as int % 2 == 0 && n as int % 4 == 0 ==> result as int == n as int / 4 - 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added precondition check before calling lemma */
    assert(valid_input(n as int));
    
    proof {
        assert(n as int > 0) by {
            assert(valid_input(n as int));
        };
        if n % 2 == 0 {
            lemma_even_number_alternatives(n as int);
        }
    }
    
    if n % 2 == 1 {
        // Odd numbers have no valid rectangles
        0
    } else if n % 4 == 2 {
        // Numbers of form 4k+2 have exactly k valid rectangles
        n / 4
    } else {
        // Numbers of form 4k have k-1 valid rectangles
        n / 4 - 1
    }
}
// </vc-code>


}

fn main() {}