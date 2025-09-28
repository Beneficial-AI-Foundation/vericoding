// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= x <= 200
}

spec fn can_have_exactly_cats(a: int, b: int, x: int) -> bool {
    a <= x <= a + b
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8) -> (result: String)
    requires valid_input(a as int, b as int, x as int)
    ensures result@ =~= seq!['Y', 'E', 'S'] <==> can_have_exactly_cats(a as int, b as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement spec logic with executable code, avoiding overflow */
    // The condition is a <= x <= a + b.
    // The sum a + b might overflow i8 (e.g., 100 + 100 = 200 > 127).
    // We cast to a larger type like i16 to perform the check in executable code.
    if a <= x && (x as i16) <= (a as i16) + (b as i16) {
        String::from_str("YES")
    } else {
        String::from_str("NO")
    }
}
// </vc-code>


}

fn main() {}