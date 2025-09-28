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
/* helper modified by LLM (iteration 5): relate count_valid_rectangles to closed-form for i8-range */
proof fn count_fits_i8(n: int)
    requires
        0 < n && n <= 127,
    ensures
        count_valid_rectangles(n) == if n % 2 == 1 { 0 } else if n % 4 == 2 { n / 4 } else { n / 4 - 1 },
{
    if n % 2 == 1 {
        assert(count_valid_rectangles(n) == 0);
    } else if n % 4 == 2 {
        assert(count_valid_rectangles(n) == n / 4);
    } else {
        assert(count_valid_rectangles(n) == n / 4 - 1);
    }
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
    /* code modified by LLM (iteration 5): compute result using i8 arithmetic and prove equality via lemma */
    let res: i8;
    if n % 2 == 1 {
        res = 0;
    } else if n % 4 == 2 {
        res = n / 4;
    } else {
        res = n / 4 - 1;
    }
    proof {
        let n_int: int = n as int;
        assert(n_int > 0);
        assert(n_int <= 127);
        count_fits_i8(n_int);
        let expected: int = if n_int % 2 == 1 { 0 } else if n_int % 4 == 2 { n_int / 4 } else { n_int / 4 - 1 };
        assert(res as int == expected);
    }
    res
}

// </vc-code>


}

fn main() {}