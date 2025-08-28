use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed for helper code, spec functions, or proofs
// </vc-helpers>

// <vc-spec>
fn conditional_average(vals_1: &Vec<u64>, vals_2: &Vec<u64>, conds_1: &Vec<bool>, conds_2: &Vec<bool>, avgs: &mut Vec<u64>) 
    // pre-conditions-start
    requires 
        vals_1.len() == vals_2.len(),
        vals_1.len() == conds_1.len(),
        vals_1.len() == conds_2.len(),
        forall |idx:int| 0 <= idx < vals_1.len() ==> conds_1[idx] || conds_2[idx],
        forall |idx:int| 0 <= idx < vals_1.len() ==> vals_1[idx] < 1000,
        forall |idx:int| 0 <= idx < vals_2.len() ==> vals_2[idx] < 1000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        avgs.len() == vals_1.len(),
        forall |idx:int| 0 <= idx < vals_1.len() ==> (
            (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
            (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
            (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
        )
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn conditional_average(vals_1: &Vec<u64>, vals_2: &Vec<u64>, conds_1: &Vec<bool>, conds_2: &Vec<bool>, avgs: &mut Vec<u64>) 
    requires 
        vals_1.len() == vals_2.len(),
        vals_1.len() == conds_1.len(),
        vals_1.len() == conds_2.len(),
        forall |idx: int| 0 <= idx < vals_1.len() ==> conds_1[idx] || conds_2[idx],
        forall |idx: int| 0 <= idx < vals_1.len() ==> vals_1[idx] < 1000,
        forall |idx: int| 0 <= idx < vals_2.len() ==> vals_2[idx] < 1000,
    ensures
        avgs.len() == vals_1.len(),
        forall |idx: int| 0 <= idx < vals_1.len() ==> (
            (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
            (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
            (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
        )
{
    let len = vals_1.len();
    avgs.clear();
    avgs.reserve(len);
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            avgs.len() == i,
            forall |idx: int| 0 <= idx < i ==> (
                (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
                (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
                (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
            ),
        decreases len - i
    {
        let avg: u64;
        if conds_1[i] && conds_2[i] {
            avg = (vals_1[i] + vals_2[i]) / 2;
        } else if conds_1[i] {
            avg = vals_1[i];
        } else {
            avg = vals_2[i];
        }
        avgs.push(avg);
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}