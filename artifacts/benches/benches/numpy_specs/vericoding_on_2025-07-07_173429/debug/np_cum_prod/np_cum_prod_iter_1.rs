use vstd::prelude::*;

verus! {

fn cum_prod(a: &[i32]) -> (res: Vec<i32>)
    ensures 
        res.len() == a.len(),
        a.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[(i-1) as int] * a[i],
{
    let mut res: Vec<i32> = Vec::new();
    
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            idx <= a.len(),
            res.len() == idx,
            idx > 0 ==> res[0] == a[0],
            forall|i: int| 1 <= i < idx ==> res[i] == res[(i-1) as int] * a[i],
        decreases a.len() - idx,
    {
        if idx == 0 {
            res.push(a[0]);
        } else {
            let prev_val = res[idx - 1];
            let curr_val = a[idx];
            assume(prev_val.checked_mul(curr_val).is_some());
            res.push(prev_val * curr_val);
        }
        idx = idx + 1;
    }
    
    res
}

fn main() {}

}