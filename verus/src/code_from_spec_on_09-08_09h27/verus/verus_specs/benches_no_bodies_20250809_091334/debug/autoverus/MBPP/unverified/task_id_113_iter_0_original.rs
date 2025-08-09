use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_digit_spec(c: u8) -> bool {
    c >= 48 && c <= 57
}

fn is_digit(c: u8) -> (res: bool)
    ensures
        res == is_digit_spec(c),
{
    return false;  // TODO: Remove this line and implement the function body
}

fn is_integer(text: &[u8]) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_spec(text[i]))),
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!
