use vstd::prelude::*;

verus! {

//IMPL all_sequence_equal_length
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
    
    for k in 1..seq.len()
        /* code modified by LLM (iteration 3): enhanced invariant to establish relationship between all checked elements */
        invariant
            forall|i: int| (0 <= i < k) ==> seq[i].len() == first_len,
            forall|i: int, j: int| (0 <= i < k && 0 <= j < k) ==> seq[i].len() == seq[j].len(),
    {
        if seq[k].len() != first_len {
            /* code modified by LLM (iteration 3): fixed type mismatch by using int casting for assertion */
            assert(seq[0].len() != seq[k as int].len());
            assert(!(forall|i: int, j: int| (0 <= i < seq.len() && 0 <= j < seq.len()) ==> seq[i].len() == seq[j].len()));
            return false;
        }
    }
    
    /* code modified by LLM (iteration 3): added assertion to help prove postcondition when returning true */
    assert(forall|i: int| (0 <= i < seq.len()) ==> seq[i].len() == first_len);
    assert(forall|i: int, j: int| (0 <= i < seq.len() && 0 <= j < seq.len()) ==> seq[i].len() == seq[j].len());
    
    true
}

} // verus!

fn main() {}