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
/* helper modified by LLM (iteration 3): fixed precondition to ensure n % 2 == 0 is satisfied before calling division lemma */
proof fn lemma_modulo_properties(n: int)
    requires n > 0
    ensures
        n % 2 == 0 || n % 2 == 1,
        n % 2 == 0 ==> (n % 4 == 0 || n % 4 == 2),
        n % 4 == 2 ==> n % 2 == 0,
        n % 4 == 0 ==> n % 2 == 0
{
}

proof fn lemma_division_properties(n: int)
    requires n > 0, n % 2 == 0
    ensures
        n / 4 >= 0,
        n % 4 == 2 ==> n / 4 >= 0,
        n % 4 == 0 ==> n / 4 >= 1
{
}

proof fn lemma_count_valid_rectangles_correct(n: int)
    requires n > 0
    ensures
        count_valid_rectangles(n) >= 0,
        n % 2 == 1 ==> count_valid_rectangles(n) == 0,
        n % 2 == 0 && n % 4 == 2 ==> count_valid_rectangles(n) == n / 4,
        n % 2 == 0 && n % 4 == 0 ==> count_valid_rectangles(n) == n / 4 - 1
{
    if n % 2 == 1 {
        assert(count_valid_rectangles(n) == 0);
    } else if n % 4 == 2 {
        assert(count_valid_rectangles(n) == n / 4);
    } else {
        assert(n % 4 == 0);
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
    /* code modified by LLM (iteration 3): only call division lemma when n is even to satisfy precondition */
    proof {
        lemma_modulo_properties(n as int);
        if n % 2 == 0 {
            lemma_division_properties(n as int);
        }
        lemma_count_valid_rectangles_correct(n as int);
    }
    
    if n % 2 == 1 {
        0
    } else if n % 4 == 2 {
        n / 4
    } else {
        n / 4 - 1
    }
}
// </vc-code>


}

fn main() {}