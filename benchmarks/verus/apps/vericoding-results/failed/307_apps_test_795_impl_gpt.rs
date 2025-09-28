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
/* helper modified by LLM (iteration 5): simple lemma relating valid_input to non-empty input */
proof fn lemma_valid_input_implies_nonempty(input: Seq<char>)
    ensures
        valid_input(input) ==> input.len() > 0,
{
    reveal(valid_input);
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
{
    /* code modified by LLM (iteration 5): construct result vector from the spec sequence using Vec::from */
    let n = extract_integer(stdin_input@);
    let k = count_pythagorean_triples_via_primitives(n);
    let s = int_to_string(k);
    let result_vec: Vec<char> = Vec::from(s);
    result_vec
}
// </vc-code>


}

fn main() {}