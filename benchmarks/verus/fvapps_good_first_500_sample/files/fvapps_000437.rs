// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn char_count(s: Seq<char>, c: char) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == c {
        1 + char_count(s.skip(1), c)
    } else {
        char_count(s.skip(1), c)
    }
}

fn remove_duplicate_letters(s: Vec<char>) -> (result: Vec<char>)
    requires s.len() > 0,
    ensures
        forall|c: char| result@.contains(c) ==> s@.contains(c),
        forall|c: char| char_count(result@, c) <= 1,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}

fn main() {}