// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit_sepc(c: char) -> (res: bool) {
    (c as u32) >= 48 && (c as u32) <= 57
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added exec helper for digit check */
fn is_digit(c: char) -> (result: bool)
    ensures result == is_digit_sepc(c)
{
    (c as u32) >= 48 && (c as u32) <= 57
}
// </vc-helpers>

// <vc-spec>
fn is_integer(text: &Vec<char>) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed to use exec call for digit check */
{
    let mut i = 0;
    while i < text.len()
        invariant
            forall |j: int| 0 <= j < i ==> is_digit_sepc(text[j])
        decreases text.len() - i
    {
        if !is_digit(text[i]) {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}