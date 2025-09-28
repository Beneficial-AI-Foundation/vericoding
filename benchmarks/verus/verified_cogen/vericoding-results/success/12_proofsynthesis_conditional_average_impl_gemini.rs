// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type mismatch in proof block by casting usize to int */
{
    let mut i: usize = 0;
    avgs.clear();

    while i < vals_1.len()
        invariant
            vals_1.len() == vals_2.len(),
            vals_1.len() == conds_1.len(),
            vals_1.len() == conds_2.len(),
            i <= vals_1.len(),
            avgs.len() == i,
            forall |idx:int| 0 <= idx < vals_1.len() ==> conds_1@[idx] || conds_2@[idx],
            forall |idx:int| 0 <= idx < vals_1.len() ==> vals_1@[idx] < 1000,
            forall |idx:int| 0 <= idx < vals_2.len() ==> vals_2@[idx] < 1000,
            forall |idx:int| 0 <= idx < i ==> (
                (conds_1@[idx] && conds_2@[idx] ==> avgs@[idx] == (vals_1@[idx] + vals_2@[idx]) / 2) &&
                (conds_1@[idx] && !conds_2@[idx] ==> avgs@[idx] == vals_1@[idx]) &&
                (!conds_1@[idx] && conds_2@[idx] ==> avgs@[idx] == vals_2@[idx])
            )
        decreases vals_1.len() - i
    {
        let v1 = vals_1[i];
        let v2 = vals_2[i];
        let c1 = conds_1[i];
        let c2 = conds_2[i];

        let avg_val = if c1 && c2 {
            (v1 + v2) / 2
        } else if c1 {
            v1
        } else {
            proof {
                assert(conds_1@[i as int] || conds_2@[i as int]);
            }
            v2
        };

        avgs.push(avg_val);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}