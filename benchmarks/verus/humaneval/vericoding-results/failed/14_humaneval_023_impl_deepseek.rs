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

proof fn lemma_correct_length_positive(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        0 <= correct_length(s),
{
    assert(s.len() as int >= 0);
}

/* helper modified by LLM (iteration 5): Simplified lemma by removing redundant condition */
proof fn lemma_strlen_equal(s: Seq<char>)
    ensures
        correct_length(s) == (s.len() as int),
{
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
    /* code modified by LLM (iteration 5): Simplified proof call and fixed verification */
    let chars = s.chars();
    proof { lemma_strlen_equal(s@); }
    chars.len()
}
// </vc-code>


}

fn main() {}