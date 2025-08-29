use vstd::prelude::*;


verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
}
// pure-end
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

// <vc-helpers>
proof fn count_digits_recursively_drop_first(seq: Seq<char>)
    requires seq.len() > 0
    ensures count_digits_recursively(seq) == 
        (if is_digit(seq[0]) { 1int } else { 0int }) + count_digits_recursively(seq.subrange(1, seq.len() as int))
    decreases seq.len()
{
    if seq.len() == 1 {
        assert(seq.subrange(1, 1).len() == 0);
        assert(count_digits_recursively(seq.subrange(1, 1)) == 0);
    } else {
        let tail = seq.subrange(1, seq.len() as int);
        count_digits_recursively_drop_first(tail);
        assert(count_digits_recursively(tail) == 
            count_digits_recursively(tail.drop_last()) + if is_digit(tail.last()) { 1int } else { 0int });
        assert(seq.drop_last() == seq.subrange(0, seq.len() - 1));
        assert(tail.drop_last() == seq.subrange(1, seq.len() - 1));
        assert(seq.last() == tail.last());
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn count_digits(text: &Vec<char>) -> (count: usize)
    // pre-conditions-start
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
    // pre-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < text.len()
        invariant
            i <= text.len(),
            count == count_digits_recursively(text@.subrange(0, i as int)),
    {
        /* code modified by LLM (iteration 5): fixed integer literal type annotations */
        proof {
            let next_subrange = text@.subrange(0, (i + 1) as int);
            count_digits_recursively_drop_first(next_subrange);
        }
        
        if is_digit(text[i]) {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) =~= text@);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}