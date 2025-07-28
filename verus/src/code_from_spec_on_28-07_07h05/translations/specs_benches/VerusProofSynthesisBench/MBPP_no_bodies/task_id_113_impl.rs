use vstd::prelude::*;

verus! {

spec fn is_digit_sepc(c: char) -> (res: bool) {
    (c as u32) >= 48 && (c as u32) <= 57
}
// pure-end

fn is_digit(c: char) -> (res: bool)
    // post-conditions-start
    ensures
        res == is_digit_sepc(c),
    // post-conditions-end
{
    (c as u32) >= 48 && (c as u32) <= 57
}

fn is_integer(text: &Vec<char>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
    // post-conditions-end
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|j: int| 0 <= j < i ==> is_digit_sepc(text[j]),
        decreases text.len() - i,
    {
        if !is_digit(text[i]) {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!

fn main() {}