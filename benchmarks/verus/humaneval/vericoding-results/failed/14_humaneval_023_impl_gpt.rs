// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    true
}

spec fn correct_length(s: Seq<char>) -> int {
    s.len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma relating correct_length to sequence length */
proof fn lemma_correct_length_def(s: Seq<char>)
    ensures
        correct_length(s) == (s.len() as int),
{
    assert(correct_length(s) == (s.len() as int));
}

// </vc-helpers>

// <vc-spec>
fn strlen(s: &str) -> (result: usize)
    requires valid_input(s@)
    ensures correct_length(s@) == (result as int)
{
    assume(false);
    unreached()
}
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return the length directly */
    s.len()
}
// </vc-code>


}

fn main() {}