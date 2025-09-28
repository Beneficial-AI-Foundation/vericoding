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
{
/* helper modified by LLM (iteration 5): alias parse_seq_to_int to spec extract_integer */
spec fn parse_seq_to_int(s: Seq<char>) -> int {
    extract_integer(s)
}

/* helper modified by LLM (iteration 5): alias int_to_seq to spec int_to_string */
spec fn int_to_seq(n: int) -> Seq<char> {
    int_to_string(n)
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
    /* code modified by LLM (iteration 5): use usize literals for index to avoid nat/integer mismatches */
    let n = parse_seq_to_int(stdin_input@);
    let cnt = count_pythagorean_triples_via_primitives(n);
    let seq = int_to_string(cnt);
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0usize;
    while i < seq.len()
        invariant
            i <= seq.len(),
        decreases seq.len() - i
    {
        result.push(seq@[i]);
        i = i + 1usize;
    }
    result
}

// </vc-code>


}

fn main() {}