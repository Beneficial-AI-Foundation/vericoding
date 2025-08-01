use vstd::prelude::*;

verus! {

spec fn count_boolean(seq: Seq<bool>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

/* code modified by LLM (iteration 3): added helper lemma to prove relationship between consecutive prefixes */
proof fn lemma_count_boolean_extend(seq: Seq<bool>, i: int)
    requires 0 < i <= seq.len()
    ensures count_boolean(seq.take(i)) == count_boolean(seq.take(i-1)) + if seq[i-1] { 1 as int } else { 0 as int }
{
    let prefix_i = seq.take(i);
    let prefix_i_minus_1 = seq.take(i-1);
    
    assert(prefix_i == prefix_i_minus_1.push(seq[i-1]));
    assert(prefix_i.drop_last() == prefix_i_minus_1);
    assert(prefix_i.last() == seq[i-1]);
}

// pure-end

fn count_true(arr: &Vec<bool>) -> (count: u64)
    // pre-conditions-start
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
    // pre-conditions-end
{
    let mut count = 0u64;
    let mut i = 0usize;
    
    /* code modified by LLM (iteration 4): restructured loop body to maintain invariant and added proof with helper lemma */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.take(i as int)) == count,
        decreases arr.len() - i,
    {
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
        
        /* code modified by LLM (iteration 4): wrap proof function call in proof block to handle ghost context */
        proof {
            lemma_count_boolean_extend(arr@, i as int);
        }
    }
    
    assert(arr@.take(arr.len() as int) == arr@);
    count
}

} // verus!

fn main() {}