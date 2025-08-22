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

/* code modified by LLM (iteration 4): Added executable version of is_upper_case for use in loop body */
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    (c as u32) >= 65 && (c as u32) <= 90
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

/* code modified by LLM (iteration 4): Added helper function to count from beginning */
spec fn count_uppercase_from_start(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        (if is_upper_case(seq[0]) { 1 as int } else { 0 as int }) + count_uppercase_from_start(seq.subrange(1, seq.len() as int))
    }
}

/* code modified by LLM (iteration 4): Added lemma to prove equivalence between the two counting methods */
proof fn lemma_count_equivalence(seq: Seq<char>)
    ensures count_uppercase_recursively(seq) == count_uppercase_from_start(seq)
    decreases seq.len()
{
    if seq.len() == 0 {
        // Base case is trivial
    } else {
        lemma_count_equivalence(seq.drop_last());
        lemma_count_equivalence(seq.subrange(1, seq.len() as int));
        
        // The recursive calls should be equivalent
        assert(seq.drop_last() == seq.subrange(0, seq.len() - 1));
        assert(seq.subrange(1, seq.len() as int) == seq.drop_first());
    }
}

/* code modified by LLM (iteration 4): Added lemma to relate subrange counting */
proof fn lemma_subrange_count(seq: Seq<char>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_uppercase_from_start(seq.subrange(0, i)) == 
            if i == 0 { 0 } else { 
                count_uppercase_from_start(seq.subrange(0, i-1)) + 
                if is_upper_case(seq[i-1]) { 1 } else { 0 }
            }
    decreases i
{
    if i == 0 {
        // Base case
    } else {
        let prefix = seq.subrange(0, i);
        let prev_prefix = seq.subrange(0, i-1);
        
        if i == 1 {
            assert(prefix.len() == 1);
            assert(prefix[0] == seq[0]);
        } else {
            assert(prefix == prev_prefix.push(seq[i-1]));
            lemma_subrange_count(seq, i-1);
        }
    }
}

fn count_uppercase(text: &Vec<char>) -> (count: u64)
    // post-conditions-start
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
    // post-conditions-end
{
    /* code modified by LLM (iteration 4): Added proof that the two counting methods are equivalent */
    lemma_count_equivalence(text@);
    
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 4): Updated loop invariant and added proof steps */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_uppercase_from_start(text@.subrange(0, i as int)) == count,
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 4): Fixed ghost variable usage in proof block */
        proof {
            let ghost next_i: int = i as int + 1;
            lemma_subrange_count(text@, next_i);
        }
        
        /* code modified by LLM (iteration 4): Changed to use executable version of is_upper_case */
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added final proof step */
    assert(text@.subrange(0, i as int) == text@);
    
    count
}

} // verus!

fn main() {}