use vstd::prelude::*;

fn main() {
    let lists = vec![
        vec![1, 2],
        vec![3, 4, 5, 6],
        vec![7],
    ];
    let max_list = max_length_list(&lists);
    println!("Max length list has {} elements", max_list.len());
}

verus! {

fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@),
{
    let mut max_idx = 0;
    let mut i = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < seq.len()
        invariant
            0 <= max_idx < seq.len(),
            1 <= i <= seq.len(),
            forall|k: int| 0 <= k < i ==> seq[max_idx as int].len() >= seq[k].len(),
        decreases seq.len() - i,
    {
        if seq[i].len() > seq[max_idx].len() {
            max_idx = i;
        }
        i += 1;
    }
    
    &seq[max_idx]
}

} // verus!