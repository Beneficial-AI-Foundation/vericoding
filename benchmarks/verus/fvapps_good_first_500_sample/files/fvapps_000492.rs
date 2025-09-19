// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_spaces(s: Seq<char>) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if s[0] == ' ' { 1int } else { 0int }) + count_spaces(s.skip(1))
    }
}

spec fn word_count(s: Seq<char>) -> int {
    count_spaces(s) + 1int
}

fn arrange_words(s: String) -> (result: String)
    requires s@.len() > 0,
    ensures
        result@.len() > 0,
        word_count(s@) == word_count(result@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}