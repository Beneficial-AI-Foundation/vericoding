use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
}
// pure-end

/* code modified by LLM (iteration 1): Added executable version of is_digit for use in implementation */
fn is_digit_exec(c: char) -> (result: bool)
    ensures result == is_digit(c)
{
    (c as u8) >= 48 && (c as u8) <= 57
}

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
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    /* code modified by LLM (iteration 1): Fixed function structure, moved ensures clause before body, implemented proper function body */
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_digits_recursively(text@.take(i as int)) == count,
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 1): Changed to use executable version of is_digit */
        if is_digit_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 1): Added assertion to help verification */
    assert(text@.take(text.len() as int) == text@);
    count
}

} // verus!

fn main() {}