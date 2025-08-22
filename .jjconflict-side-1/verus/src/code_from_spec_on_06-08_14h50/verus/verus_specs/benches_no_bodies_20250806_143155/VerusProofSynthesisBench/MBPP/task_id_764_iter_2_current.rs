use vstd::prelude::*;


verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
}

/* code modified by LLM (iteration 1): added executable version of is_digit function */
fn is_digit_exec(c: char) -> (result: bool)
    ensures result == is_digit(c)
{
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
    let mut count = 0;
    let mut i = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_digits_recursively(text@.subrange(0, i as int)) == count,
    {
        /* code modified by LLM (iteration 1): replaced is_digit with is_digit_exec for executable code */
        if is_digit_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

} // verus!

fn main() {}