use vstd::prelude::*;

fn main() {
    // Example usage
    let c = 52u8; // ASCII for '4'
    let result = is_digit(c);
    println!("Is '4' a digit? {}", result);
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
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
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