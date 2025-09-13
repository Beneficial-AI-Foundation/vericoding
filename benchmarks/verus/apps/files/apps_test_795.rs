// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: &str) -> bool {
    input.len() > 0
}

spec fn valid_n(n: int) -> bool {
    n >= 1 && n <= 10000
}

#[verifier::uninterp]
spec fn integer_square_root(n: int) -> int;

#[verifier::uninterp]
spec fn count_from_primitives(n: int, m: int, a: int, b: int) -> int;

#[verifier::uninterp]
spec fn extract_integer(input: &str) -> int;

#[verifier::uninterp]
spec fn int_to_string(n: int) -> String;

spec fn count_pythagorean_triples_via_primitives(n: int) -> int {
    if valid_n(n) {
        let m = integer_square_root(n);
        count_from_primitives(n, m, 1, 1)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires 
        valid_input(stdin_input),
    ensures 
        result.len() > 0,
        result == int_to_string(count_pythagorean_triples_via_primitives(extract_integer(stdin_input))),
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}