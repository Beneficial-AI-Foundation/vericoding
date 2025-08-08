use vstd::prelude::*;

verus! {

fn cum_sum(a: &[i32]) -> (res: Vec<i32>)
    requires a.len() < usize::MAX,
    ensures
        res.len() == a.len(),
        res.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1].wrapping_add(a[i]),
{
    let mut res = Vec::with_capacity(a.len());
    
    if a.len() > 0 {
        res.push(a[0]);
        
        let mut i = 1usize;
        while i < a.len()
            invariant
                1 <= i <= a.len(),
                res.len() == i,
                res[0] == a[0],
                forall|j: int| 1 <= j < i ==> #[trigger] res[j] == res[j-1].wrapping_add(a[j]),
            decreases a.len() - i,
        {
            let prev_val = res[i-1];
            let new_val = prev_val.wrapping_add(a[i]);
            res.push(new_val);
            i = i + 1;
        }
    }
    
    res
}

fn main() {}

}