use vstd::prelude::*;

verus! {

fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    // pre-conditions-start
    requires
        seq.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
    // post-conditions-end
{
    let first_len = seq[0].len();
    
    /* code modified by LLM (iteration 2): Updated loop invariant to properly establish postcondition */
    for k in 1..seq.len()
        invariant
            forall|i: int| (0 <= i < k) ==> seq[i].len() == first_len,
    {
        if seq[k].len() != first_len {
            /* code modified by LLM (iteration 2): Added proof that forall condition is false when returning false */
            assert(seq[0].len() == first_len);
            assert(seq[k as int].len() != first_len);
            assert(0 <= 0 < seq.len() && 0 <= k < seq.len());
            assert(seq[0].len() != seq[k as int].len());
            assert(!(forall|i: int, j: int|
                (0 <= i < seq.len() && 0 <= j < seq.len()) ==> seq[i].len() == seq[j].len()));
            return false;
        }
    }
    
    /* code modified by LLM (iteration 2): Added assertion to help prove postcondition when returning true */
    assert(forall|i: int| (0 <= i < seq.len()) ==> seq[i].len() == first_len);
    
    /* code modified by LLM (iteration 2): Added proof that if all have same length as first, then all have same length as each other */
    assert(forall|i: int, j: int| (0 <= i < seq.len() && 0 <= j < seq.len()) ==> 
        seq[i].len() == first_len && seq[j].len() == first_len);
    
    true
}

} // verus!

fn main() {}