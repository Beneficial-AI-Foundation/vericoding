use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    (c as u32) >= 97 && (c as u32) <= 122
}
// pure-end

spec fn is_upper_case(c: char) -> (result: bool) {
    (c as u32) >= 65 && (c as u32) <= 90
}
// pure-end

/* code modified by LLM (iteration 1): added executable version of is_upper_case for use in function body */
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    let code = c as u32;
    code >= 65 && code <= 90
}

spec fn count_uppercase_recursively(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

fn count_uppercase(text: &Vec<char>) -> (count: u64)
    // post-conditions-start
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
    // post-conditions-end
{
    let mut count = 0u64;
    let mut i = 0usize;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_uppercase_recursively(text@.take(i as int)) == count,
    {
        /* code modified by LLM (iteration 1): replaced spec function call with executable version */
        if is_upper_case_exec(text[i]) {
            count += 1;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): added proof block to establish postcondition */
    proof {
        assert(text@.take(text.len() as int) =~= text@);
    }
    
    count
}

} // verus!

fn main() {}