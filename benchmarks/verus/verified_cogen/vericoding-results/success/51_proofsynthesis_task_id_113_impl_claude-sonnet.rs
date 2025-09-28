// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit_sepc(c: char) -> (res: bool) {
    (c as u32) >= 48 && (c as u32) <= 57
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added ensures clause to link with spec function */
fn is_digit(c: char) -> (result: bool)
    ensures
        result == is_digit_sepc(c),
{
    let code = c as u32;
    code >= 48 && code <= 57
}
// </vc-helpers>

// <vc-spec>
fn is_integer(text: &Vec<char>) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix compilation error */
    let mut i = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|j: int| 0 <= j < i ==> is_digit_sepc(text[j]),
        decreases text.len() - i
    {
        if !is_digit(text[i]) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}