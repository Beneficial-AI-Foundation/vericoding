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

/* code modified by LLM (iteration 2): added executable version of is_upper_case */
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
    let mut i = 0usize;
    
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_uppercase_recursively(text@.take(i as int)) == count,
        decreases text.len() - i
    {
        /* code modified by LLM (iteration 2): use executable version of is_upper_case */
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        /* code modified by LLM (iteration 2): cast nat to int for take method */
        assert(text@.take(text@.len() as int) =~= text@);
    }
    
    count
}

} // verus!