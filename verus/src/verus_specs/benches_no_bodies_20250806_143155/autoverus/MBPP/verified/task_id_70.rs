use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    requires
        seq.len() > 0,
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!
