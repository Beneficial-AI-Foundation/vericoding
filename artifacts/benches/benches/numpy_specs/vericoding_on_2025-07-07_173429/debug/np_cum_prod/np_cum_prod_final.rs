use vstd::prelude::*;

verus! {

fn cum_prod(a: &[i32]) -> (res: Vec<i32>)
    ensures
        res.len() == a.len(),
        res.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] * a[i],
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            i > 0 ==> res[0] == a[0],
            forall|j: int| 1 <= j < i ==> res[j] == res[j-1] * a[j],
        decreases a.len() - i,
    {
        if i == 0 {
            res.push(a[0]);
        } else {
            let prev_val = res[i-1];
            let curr_val = a[i];
            assume(i32::MIN <= prev_val * curr_val <= i32::MAX);
            let next_val = prev_val * curr_val;
            res.push(next_val);
        }
        i += 1;
    }
    
    res
}

fn main() {}

} // verus!