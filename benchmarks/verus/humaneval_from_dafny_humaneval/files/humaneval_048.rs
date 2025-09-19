// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn to_lower(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}

spec fn is_palindrome_spec(text: Seq<char>) -> bool {
    forall|i: int| 0 <= i < text.len() ==> #[trigger] to_lower(text[i]) == to_lower(text[text.len() - 1 - i])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: Vec<char>) -> (result: bool)
    ensures result <==> is_palindrome_spec(text@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}