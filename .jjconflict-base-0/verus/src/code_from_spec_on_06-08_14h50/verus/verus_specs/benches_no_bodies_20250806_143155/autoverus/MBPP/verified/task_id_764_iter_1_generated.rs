use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_digit(c: u8) -> bool {
    (c >= 48 && c <= 57)
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
    let mut count = 0;
    let mut i = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_digits_recursively(text@.subrange(0, i as int)) == count,
    {
        if is_digit(text[i]) {
            count = count + 1;
        }
        i = i + 1;
        
        proof {
            assert(text@.subrange(0, i as int) == text@.subrange(0, (i - 1) as int).push(text@[i as int - 1]));
        }
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) == text@);
    }
    
    count
}

} // verus!