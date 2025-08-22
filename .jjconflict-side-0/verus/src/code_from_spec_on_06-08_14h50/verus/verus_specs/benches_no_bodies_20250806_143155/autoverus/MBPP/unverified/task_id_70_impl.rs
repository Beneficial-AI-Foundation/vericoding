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
    
    for i in 1..seq.len()
        invariant
            forall|k: int| (0 <= k < i) ==> seq[k].len() == first_len,
    {
        if seq[i].len() != first_len {
            return false;
        }
    }
    
    true
}

} // verus!