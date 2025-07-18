use vstd::prelude::*;

verus! {

fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    requires
        seq.len() > 0,
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
{
    /* code modified by LLM (iteration 2): strengthened loop invariant to maintain relationship with postcondition */
    let first_len = seq[0].len();
    
    for i in 0..seq.len()
        invariant
            forall|k: int| (0 <= k < i) ==> seq[k].len() == first_len,
            forall|k1: int, k2: int| (0 <= k1 < i && 0 <= k2 < i) ==> seq[k1].len() == seq[k2].len(),
    {
        if seq[i].len() != first_len {
            /* code modified by LLM (iteration 2): added assertion to help prove postcondition when returning false */
            assert(seq[0].len() != seq[i].len());
            assert(!(forall|k1: int, k2: int| (0 <= k1 < seq.len() && 0 <= k2 < seq.len()) ==> seq[k1].len() == seq[k2].len()));
            return false;
        }
    }
    
    /* code modified by LLM (iteration 2): added assertion to help prove postcondition when returning true */
    assert(forall|k: int| (0 <= k < seq.len()) ==> seq[k].len() == first_len);
    assert(forall|k1: int, k2: int| (0 <= k1 < seq.len() && 0 <= k2 < seq.len()) ==> seq[k1].len() == seq[k2].len());
    
    true
}

} // verus!

fn main() {}