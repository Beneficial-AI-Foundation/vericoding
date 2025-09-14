// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit_sepc(c: char) -> (res: bool) {
    (c as u32) >= 48 && (c as u32) <= 57
}
// </vc-preamble>

// <vc-helpers>
fn is_digit(c: char) -> (res: bool)
    ensures
        res == is_digit_sepc(c),
{
    let c_val = c as u32;
    c_val >= 48 && c_val <= 57
}
// </vc-helpers>

// <vc-spec>
fn is_integer(text: &Vec<char>) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut i: usize = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|j: int| 0 <= j < i ==> is_digit_sepc(text[j]),
        decreases text.len() - i,
    {
        if !is_digit(text[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}