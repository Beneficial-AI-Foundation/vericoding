// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> (result: bool) {
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added exec mode function to enable calling from exec code */
exec fn is_digit_exec(c: char) -> (result: bool)
    ensures result == is_digit(c)
{
    let byte_val = c as u8;
    byte_val >= 48 && byte_val <= 57
}

proof fn lemma_count_digits_drop_last(seq: Seq<char>, i: int)
    requires 0 <= i < seq.len()
    ensures count_digits_recursively(seq.take(i as int)) + (if is_digit(seq[i]) { 1int } else { 0int }) == count_digits_recursively(seq.take((i + 1) as int))
{
    let prefix = seq.take(i as int);
    let prefix_plus_one = seq.take((i + 1) as int);
    assert(prefix_plus_one == prefix.push(seq[i]));
    assert(prefix_plus_one.drop_last() == prefix);
    assert(prefix_plus_one.last() == seq[i]);
}
// </vc-helpers>

// <vc-spec>
fn count_digits(text: &Vec<char>) -> (count: usize)

    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): replaced spec function call with exec function call */
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            count == count_digits_recursively(text@.take(i as int)),
            count <= i,
        decreases text.len() - i
    {
        if is_digit_exec(text[i]) {
            count = count + 1;
        }
        
        proof {
            lemma_count_digits_drop_last(text@, i as int);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.take(i as int) == text@);
    }
    
    count
}
// </vc-code>

}
fn main() {}