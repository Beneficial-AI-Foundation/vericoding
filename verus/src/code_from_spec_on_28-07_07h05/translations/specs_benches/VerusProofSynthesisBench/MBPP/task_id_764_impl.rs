use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
}

/* code modified by LLM (iteration 4): Added executable version of is_digit for use in implementation */
fn is_digit_exec(c: char) -> (result: bool)
    ensures result == is_digit(c)
{
    let byte_val = c as u8;
    byte_val >= 48 && byte_val <= 57
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

/* code modified by LLM (iteration 4): Fixed integer literal type annotations to resolve compilation error */
proof fn lemma_count_digits_prefix(seq: Seq<char>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_digits_recursively(seq.take(i)) == 
        count_digits_recursively(seq.take(i - 1)) + 
        if i > 0 && is_digit(seq[i - 1]) { 1int } else { 0int }
    decreases i
{
    if i == 0 {
        assert(seq.take(0) =~= Seq::<char>::empty());
    } else {
        let prefix = seq.take(i);
        let shorter_prefix = seq.take(i - 1);
        assert(prefix.len() == i);
        assert(prefix.last() == seq[i - 1]);
        assert(prefix.drop_last() =~= shorter_prefix);
    }
}

fn count_digits(text: &Vec<char>) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): Updated loop invariant and added proof annotations */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_digits_recursively(text@.take(i as int)) == count,
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 4): Added lemma call to maintain invariant */
        proof {
            lemma_count_digits_prefix(text@, (i + 1) as int);
        }
        
        /* code modified by LLM (iteration 4): Changed is_digit call to is_digit_exec for executable context */
        if is_digit_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(text@.take(text.len() as int) == text@);
    count
}

} // verus!

fn main() {}