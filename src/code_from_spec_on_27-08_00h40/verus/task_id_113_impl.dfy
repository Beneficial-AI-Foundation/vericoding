use vstd::prelude::*;

verus! {

spec fn is_digit_sepc(c: char) -> (res: bool) {
    (c as u32) >= 48 && (c as u32) <= 57
}
// pure-end

// <vc-helpers>
fn is_digit(c: char) -> (res: bool)
    ensures
        res == is_digit_sepc(c),
{
    (c as u32) >= 48 && (c as u32) <= 57
}
// </vc-helpers>

// <vc-spec>
fn is_integer(text: &Vec<char>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|j: int| 0 <= j < i ==> is_digit_sepc(text[j]),
    {
        if !is_digit(text[i]) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

} // verus!

fn main() {}