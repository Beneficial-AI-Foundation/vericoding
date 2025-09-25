// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit_sepc(c: char) -> (res: bool) {
    (c as u32) >= 48 && (c as u32) <= 57
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_integer(text: &Vec<char>) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}