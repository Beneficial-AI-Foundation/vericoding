use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

/* code modified by LLM (iteration 1): Added executable version of is_upper_case function */
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
            count == count_uppercase_recursively(text@.subrange(0, i as int)),
    {
        /* code modified by LLM (iteration 1): Use executable version of is_upper_case */
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        
        proof {
            assert(text@.subrange(0, i as int + 1) == text@.subrange(0, i as int).push(text@[i as int]));
            lemma_count_recursive_push(text@.subrange(0, i as int), text@[i as int]);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) == text@);
    }
    
    count
}

proof fn lemma_count_recursive_push(seq: Seq<u8>, elem: u8)
    ensures count_uppercase_recursively(seq.push(elem)) == count_uppercase_recursively(seq) + if is_upper_case(elem) { 1 as int } else { 0 as int }
{
    if seq.len() == 0 {
        assert(seq.push(elem).drop_last() == seq);
        assert(seq.push(elem).last() == elem);
    } else {
        assert(seq.push(elem).drop_last() == seq.drop_last().push(elem));
        assert(seq.push(elem).last() == elem);
        lemma_count_recursive_push(seq.drop_last(), elem);
    }
}

} // verus!