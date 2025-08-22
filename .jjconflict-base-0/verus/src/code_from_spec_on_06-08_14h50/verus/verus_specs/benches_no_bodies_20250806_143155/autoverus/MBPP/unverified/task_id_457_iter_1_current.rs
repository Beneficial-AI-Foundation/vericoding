use vstd::prelude::*;

fn main() {}

verus! {

fn min_sublist(seq: &Vec<Vec<i32>>) -> (min_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> min_list.len() <= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && min_list@ =~= #[trigger] (seq[k]@),
{
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < seq.len()
        invariant
            0 <= min_idx < seq.len(),
            1 <= i <= seq.len(),
            forall|k: int| 0 <= k < i ==> seq[min_idx as int].len() <= #[trigger] (seq[k]).len(),
    {
        if seq[i].len() < seq[min_idx].len() {
            min_idx = i;
        }
        i += 1;
    }
    
    &seq[min_idx]
}

} // verus!