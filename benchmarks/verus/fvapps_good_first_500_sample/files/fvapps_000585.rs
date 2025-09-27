// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_char_occurrences(text: Seq<char>, ch: char) -> nat
    decreases text.len()
{
    if text.len() == 0 {
        0
    } else {
        let count_rest = count_char_occurrences(text.skip(1), ch);
        if text[0] == ch {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

spec fn starts_with_char(text: Seq<char>, ch: char) -> bool {
    text.len() > 0 && text[0] == ch
}

spec fn ends_with_char(text: Seq<char>, ch: char) -> bool {
    text.len() > 0 && text[text.len() - 1] == ch
}

fn process_text(text: &str) -> (result: String)
    requires text@.len() > 0,
    ensures 
        result@.len() > 0,
        starts_with_char(result@, 'I') && ends_with_char(result@, 'I')
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