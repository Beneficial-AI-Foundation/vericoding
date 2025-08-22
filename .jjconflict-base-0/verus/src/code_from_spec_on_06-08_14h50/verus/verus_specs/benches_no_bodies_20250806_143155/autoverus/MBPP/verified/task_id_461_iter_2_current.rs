use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

/* code modified by LLM (iteration 1): Added exec function to check if character is uppercase */
fn is_upper_case_exec(c: u8) -> (result: bool)
    ensures result == is_upper_case(c)
{
    c >= 65 && c <= 90
}

spec fn count_uppercase_recursively(seq: Seq<u8>) -> int
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

fn count_uppercase(text: &[u8]) -> (count: u64)
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
{
    let mut count = 0u64;
    let mut i = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_uppercase_recursively(text@.subrange(0, i as int)) == count,
    {
        /* code modified by LLM (iteration 1): Changed spec function call to exec function call */
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        
        proof {
            assert(text@.subrange(0, i as int + 1) == text@.subrange(0, i as int).push(text@[i as int]));
            assert(count_uppercase_recursively(text@.subrange(0, i as int + 1)) == 
                   count_uppercase_recursively(text@.subrange(0, i as int)) + 
                   if is_upper_case(text@[i as int]) { 1 as int } else { 0 as int });
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) == text@);
    }
    
    count
}

} // verus!