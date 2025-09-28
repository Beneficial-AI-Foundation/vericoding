// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_n(n: int) -> bool {
    n >= 1 && n <= 10000
}

spec fn integer_square_root(n: int) -> int {
    0  /* placeholder implementation */
}

spec fn count_from_primitives(n: int, m: int, u: int, v: int) -> int {
    0  /* placeholder implementation */
}

spec fn extract_integer(input: Seq<char>) -> int {
    0  /* placeholder implementation */
}

spec fn int_to_string(n: int) -> Seq<char> {
    seq![]  /* placeholder implementation */
}

spec fn count_pythagorean_triples_via_primitives(n: int) -> int {
    let m = integer_square_root(n);
    count_from_primitives(n, m, 1, 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added return type to match expected integer division output */
spec fn s_a(n: int, a: int, a_square: int) -> int
    requires
        n >= 1,
        a >= 1,
        a_square == a * a
    ensures
        s_a(n, a, a_square) == (n - a_square) / (2 * a)
{
    (n - a_square) / (2 * a)
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures 
        result@.len() > 0,
        result@ == int_to_string(count_pythagorean_triples_via_primitives(extract_integer(stdin_input@)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed to_vec() call and added result from int_to_string*/
{
    let n_val = extract_integer(stdin_input@);
    let result_count = count_pythagorean_triples_via_primitives(n_val);
    int_to_string(result_count).to_vec()
}
// </vc-code>


}

fn main() {}