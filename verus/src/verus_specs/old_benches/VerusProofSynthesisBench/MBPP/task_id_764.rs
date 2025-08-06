use vstd::prelude::*;


verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
}
// pure-end

spec fn count_digits_recursively(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

fn count_digits(text: &Vec<char>) -> (count: usize)
    // pre-conditions-start
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
    // pre-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
