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

/* code modified by LLM (iteration 1): Added exec function is_upper_case_exec to call from exec mode */
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    let code = c as u32;
    code >= 65 && code <= 90
}

fn count_uppercase(text: &Vec<char>) -> (count: u64)
    // post-conditions-start
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
    // post-conditions-end
{
    let mut count = 0u64;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): Added decreases clause to satisfy Verus requirement */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_uppercase_recursively(text@.take(i as int)),
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 1): Changed is_upper_case to is_upper_case_exec for exec mode compatibility */
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

} // verus!

fn main() {}