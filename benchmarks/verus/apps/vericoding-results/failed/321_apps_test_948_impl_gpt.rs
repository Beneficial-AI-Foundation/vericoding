// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_grid(grid: Seq<Seq<char>>, n: int, m: int) -> bool {
    n >= 1 && m >= 1 && grid.len() == n &&
    forall|i: int| 0 <= i < grid.len() ==> grid[i].len() == m
}

spec fn count_face_squares(input: Seq<char>) -> int
    decreases input.len()
{
    if input.len() == 0 {
        0
    } else {
        /* Parse input and count valid face squares */
        0  /* Placeholder - actual implementation would parse lines and count squares */
    }
}

spec fn count_face_squares_as_string(input: Seq<char>) -> Seq<char> {
    /* Convert count to string representation */
    seq!['0', '\n']  /* Placeholder */
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma showing the result string is always the constant "0\n" */
proof fn lemma_result_is_zero_newline(input: Seq<char>)
    ensures
        count_face_squares_as_string(input) == seq!['0', '\n'],
{
    assert(count_face_squares_as_string(input) == seq!['0', '\n']);
}

// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires 
        valid_input(input@),
    ensures 
        result@.len() > 0,
        result@ == count_face_squares_as_string(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): mutate the given input String in-place to "0\n" without constructing a new String */
    proof {
        lemma_result_is_zero_newline(input@);
        assert(count_face_squares_as_string(input@) == seq!['0', '\n']);
    }
    let mut r = input;
    r.clear();
    r.push('0');
    r.push('\n');
    proof {
        assert(r@ == seq!['0', '\n']);
    }
    r
}
// </vc-code>


}

fn main() {}