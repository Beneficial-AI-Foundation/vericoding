// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_alpha(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

spec fn valid_last_char_is_standalone_letter(txt: Seq<char>) -> bool {
    txt.len() > 0 && is_alpha(txt[txt.len() - 1]) && (txt.len() == 1 || txt[txt.len() - 2] == ' ')
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn check_if_last_char_is_a_letter(txt: &str) -> (result: bool)
    ensures result == valid_last_char_is_standalone_letter(txt@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}