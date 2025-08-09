use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_digit_sepc(c: u8) -> bool {
    c >= 48 && c <= 57
}

fn is_digit(c: u8) -> (res: bool)
    ensures
        res == is_digit_sepc(c),
{
    c >= 48 && c <= 57
}

fn is_integer(text: &[u8]) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
{
    let mut i = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|j: int| 0 <= j < i ==> is_digit_sepc(text[j]),
        /* code modified by LLM (iteration 1): added decreases clause to ensure loop termination */
        decreases text.len() - i
    {
        if !is_digit(text[i]) {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!