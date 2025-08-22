use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

/* code modified by LLM (iteration 1): Added executable version of is_upper_case for use in implementation */
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

/* code modified by LLM (iteration 4): Added lemma to prove relationship between prefix counting and recursive spec */
proof fn lemma_count_prefix_step(seq: Seq<u8>, i: int)
    requires 0 <= i < seq.len()
    ensures count_uppercase_recursively(seq.take(i + 1)) == 
            count_uppercase_recursively(seq.take(i)) + if is_upper_case(seq[i]) { 1int } else { 0int }
    decreases seq.len() - i
{
    let prefix_i = seq.take(i);
    let prefix_i_plus_1 = seq.take(i + 1);
    
    if i == 0 {
        assert(prefix_i.len() == 0);
        assert(prefix_i_plus_1.len() == 1);
        assert(prefix_i_plus_1[0] == seq[0]);
        assert(count_uppercase_recursively(prefix_i) == 0);
    } else {
        assert(prefix_i_plus_1.drop_last() == prefix_i);
        assert(prefix_i_plus_1.last() == seq[i]);
        lemma_count_prefix_step(seq, i - 1);
    }
}

fn count_uppercase(text: &[u8]) -> (count: u64)
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
{
    let mut count = 0u64;
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_uppercase_recursively(text@.take(i as int)) == count,
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 3): Added proof step to maintain loop invariant */
        proof {
            lemma_count_prefix_step(text@, i as int);
        }
        
        /* code modified by LLM (iteration 1): Changed is_upper_case to is_upper_case_exec for executable code */
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(text@.take(text.len() as int) == text@);
    count
}

} // verus!