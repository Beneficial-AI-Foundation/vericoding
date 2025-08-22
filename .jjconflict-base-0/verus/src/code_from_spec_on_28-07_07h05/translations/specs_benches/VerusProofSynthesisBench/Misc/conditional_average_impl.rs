use vstd::prelude::*;

verus!{
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
{
    avgs.clear();
    
    let mut i = 0;
    /* code modified by LLM (iteration 2): added invariants including precondition preservation */
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
        decreases vals_1.len() - i
    {
        /* code modified by LLM (iteration 2): added overflow prevention and additional assertions */
        assert(i < vals_1.len());
        assert(i < conds_1.len());
        assert(i < conds_2.len());
        assert(i < vals_2.len());
        assert(vals_1[i] < 1000);
        assert(vals_2[i] < 1000);
        
        let avg_val = if conds_1[i] && conds_2[i] {
            /* code modified by LLM (iteration 2): added overflow check before division */
            assert(vals_1[i] + vals_2[i] < 2000); // Both values < 1000, so sum < 2000
            (vals_1[i] + vals_2[i]) / 2
        } else if conds_1[i] && !conds_2[i] {
            vals_1[i]
        } else {
            vals_2[i]
        };
        
        avgs.push(avg_val);
        
        /* code modified by LLM (iteration 2): added assertion to help prove invariant after push */
        assert(avgs.len() == i + 1);
        assert(forall |idx:int| 0 <= idx < i ==> (
            (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
            (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
            (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
        ));
        
        i += 1;
    }
}
}

fn main() {}