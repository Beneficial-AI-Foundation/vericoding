// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_rational_equal(s1: &str, s2: &str) -> (result: bool) {
    // impl-start
    assume(false);
    false
    // impl-end
}

fn make_rational_str(n: i32, d: i32) -> (result: String)
    requires d > 0
{
    // impl-start
    assume(false);
    "0".to_string()
    // impl-end
}

proof fn equivalent_fractions(n1: i32, d1: i32, n2: i32, d2: i32)
    requires
        d1 > 0,
        d2 > 0,
        n1 >= -1000,
        n1 <= 1000,
        d1 <= 100,
        n2 >= -1000,
        n2 <= 1000,
        d2 <= 100,
        n1 / d1 == n2 / d2,
    ensures
        is_rational_equal(&make_rational_str(n1, d1), &make_rational_str(n2, d2)) == true
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn repeating_nines(n: usize)
    requires
        n > 0,
        n <= 9,
    ensures
        is_rational_equal(&format!("0.{}(9)", "9".repeat(n)), "1.") == true
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-spec>
// <vc-code>
// </vc-code>

}

fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // Example tests commented out for verification:
    // assert(is_rational_equal("0.(52)", "0.5(25)") == true);
    // assert(is_rational_equal("0.1666(6)", "0.166(66)") == true);
    // assert(is_rational_equal("0.9(9)", "1.") == true);
}