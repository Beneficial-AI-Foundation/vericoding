use vstd::prelude::*;
fn main() {}

verus!{
fn conditional_average(vals_1: &Vec<u64>, vals_2: &Vec<u64>, conds_1: &Vec<bool>, conds_2: &Vec<bool>, avgs: &mut Vec<u64>) 
    requires 
        vals_1.len() == vals_2.len(),
        vals_1.len() == conds_1.len(),
        vals_1.len() == conds_2.len(),
        forall |idx:int| 0 <= idx < vals_1.len() ==> conds_1[idx] || conds_2[idx],
        forall |idx:int| 0 <= idx < vals_1.len() ==> vals_1[idx] < 1000,
        forall |idx:int| 0 <= idx < vals_2.len() ==> vals_2[idx] < 1000,
    ensures
        avgs.len() == vals_1.len(),
        forall |idx:int| 0 <= idx < vals_1.len() ==> (
            (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
            (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
            (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
        )
{
    avgs.set_len(0);
    
    let mut i: usize = 0;
    while i < vals_1.len()
        invariant
            i <= vals_1.len(),
            avgs.len() == i,
            vals_1.len() == vals_2.len(),
            vals_1.len() == conds_1.len(),
            vals_1.len() == conds_2.len(),
            forall |idx:int| 0 <= idx < vals_1.len() ==> conds_1[idx] || conds_2[idx],
            forall |idx:int| 0 <= idx < vals_1.len() ==> vals_1[idx] < 1000,
            forall |idx:int| 0 <= idx < vals_2.len() ==> vals_2[idx] < 1000,
            forall |idx:int| 0 <= idx < i ==> (
                (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
                (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
                (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
            )
    {
        let avg_val = if conds_1[i] && conds_2[i] {
            (vals_1[i] + vals_2[i]) / 2
        } else if conds_1[i] {
            vals_1[i]
        } else {
            vals_2[i]
        };
        
        avgs.push(avg_val);
        i += 1;
    }
}
}