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
/* helper modified by LLM (iteration 2): lemma relating concrete string length to ghost sequence length */
proof fn strlen_lemma(s: &str)
    ensures
        correct_length(s@) == (s.len() as int),
{
    // The ghost sequence s@ corresponds to the concrete string s; their lengths are equal.
    assert(s@.len() as int == s.len() as int);
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
    /* code modified by LLM (iteration 2): compute length and invoke lemma */
    let result = s.len();
    proof {
        strlen_lemma(s);
    }
    result
}
// </vc-code>


}

fn main() {}