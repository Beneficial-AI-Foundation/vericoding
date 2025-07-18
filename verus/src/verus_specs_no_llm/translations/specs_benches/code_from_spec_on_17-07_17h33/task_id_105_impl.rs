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
// pure-end

/* code modified by LLM (iteration 4): Fixed function signature by moving ensures clause before opening brace */
fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    /* code modified by LLM (iteration 4): Implemented proper counting logic with correct loop invariants and decreases clause */
    let mut count = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.subrange(0, i as int)) == count,
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 4): Added assertion to establish relationship between subranges */
        assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr@[i as int]));
        
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
        
        /* code modified by LLM (iteration 4): Added assertion to help prove invariant maintenance */
        assert(count_boolean(arr@.subrange(0, i as int)) == count);
    }
    
    /* code modified by LLM (iteration 4): Added assertion to help prove postcondition */
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    count
}

} // verus!

fn main() {}