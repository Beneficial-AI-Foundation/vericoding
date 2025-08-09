use vstd::prelude::*;

fn main() {
    let text = b"abc123def";
    let count = count_digits(text);
    println!("Digit count: {}", count);
}

verus! {

spec fn is_digit(c: u8) -> bool {
    (c >= 48 && c <= 57)
}

/* code modified by LLM (iteration 1): added executable version of is_digit function */
fn is_digit_exec(c: u8) -> (result: bool)
    ensures result == is_digit(c)
{
    c >= 48 && c <= 57
}

spec fn count_digits_recursively(seq: Seq<u8>) -> int
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

fn count_digits(text: &[u8]) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 2): added decreases clause for loop termination */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_digits_recursively(text@.subrange(0, i as int)),
        decreases text.len() - i
    {
        /* code modified by LLM (iteration 1): replaced is_digit call with is_digit_exec */
        if is_digit_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) =~= text@);
    }
    
    count
}

} // verus!