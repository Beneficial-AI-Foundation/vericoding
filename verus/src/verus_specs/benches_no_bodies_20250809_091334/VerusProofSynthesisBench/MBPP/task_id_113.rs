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
    return false;  // TODO: Remove this line and implement the function body
}

fn is_integer(text: &Vec<char>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}