// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit_sepc(c: char) -> (res: bool) {
    (c as u32) >= 48 && (c as u32) <= 57
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no functional changes */
fn is_digit_exec(c: char) -> (res: bool)
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
    /* code modified by LLM (iteration 2): added decreases clause to the while loop to prove termination */
    let mut i: usize = 0;
    while i < text.len()
        invariant
            i <= text.len(),
            forall|j: int| 0 <= j < i as int ==> is_digit_sepc(text[j]),
        decreases text.len() - i
    {
        if !is_digit_exec(text[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}