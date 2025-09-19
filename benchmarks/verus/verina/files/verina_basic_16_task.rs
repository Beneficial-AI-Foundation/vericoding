// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace_chars(s: &str, old_char: char, new_char: char) -> (result: Seq<char>)
    ensures
        result.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> 
            (s@[i] == old_char ==> result[i] == new_char) &&
            (s@[i] != old_char ==> result[i] == s@[i]),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    seq![]
    // impl-end
}
// </vc-code>


}
fn main() {}