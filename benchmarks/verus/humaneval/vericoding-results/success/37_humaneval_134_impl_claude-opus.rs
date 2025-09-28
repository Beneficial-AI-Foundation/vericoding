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
    /* code modified by LLM (iteration 2): removed invalid use of @ in exec mode */
    let len = txt.unicode_len();
    
    if len == 0 {
        return false;
    }
    
    let last_char = txt.get_char(len - 1);
    let is_letter = (last_char >= 'a' && last_char <= 'z') || (last_char >= 'A' && last_char <= 'Z');
    
    if !is_letter {
        return false;
    }
    
    if len == 1 {
        return true;
    }
    
    let second_last = txt.get_char(len - 2);
    second_last == ' '
}
// </vc-code>


}

fn main() {}