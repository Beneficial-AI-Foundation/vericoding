use vstd::prelude::*;

fn main() {}

verus! {

fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    requires
        seq.len() > 0,
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
{
    let first_len = seq[0].len();
    
    for k in 1..seq.len()
        invariant
            /* code modified by LLM (iteration 1): strengthened invariant to cover full range needed for postcondition */
            forall|i: int| (0 <= i < k) ==> seq[i].len() == first_len,
    {
        if seq[k].len() != first_len {
            /* code modified by LLM (iteration 1): added assertion to help prove postcondition on early return */
            assert(seq[k as int].len() != seq[0].len());
            return false;
        }
    }
    
    /* code modified by LLM (iteration 1): added assertion to help prove postcondition when returning true */
    assert(forall|i: int| (0 <= i < seq.len()) ==> seq[i].len() == first_len);
    true
}

} // verus!