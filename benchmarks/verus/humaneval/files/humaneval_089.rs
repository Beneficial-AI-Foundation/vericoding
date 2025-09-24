// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn encrypt_char(c: char) -> char {
    if 'a' <= c && c <= 'z' {
        (((c as int - 'a' as int + 4) % 26) + 'a' as int) as char
    } else if 'A' <= c && c <= 'Z' {
        (((c as int - 'A' as int + 4) % 26) + 'A' as int) as char
    } else {
        c
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn encrypt(s: Vec<char>) -> (result: Vec<char>)
    requires s@.len() >= 0
    ensures result@.len() == s@.len(),
            forall|i: int| 0 <= i < s@.len() ==> #[trigger] result@[i] == #[trigger] encrypt_char(#[trigger] s@[i])
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