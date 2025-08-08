use vstd::prelude::*;

verus! {

fn add(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> add_overflow_safe(a[i], b[i]),
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == a[i] + b[i],
{
    let mut res = Vec::with_capacity(a.len());
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            res.len() == idx,
            a.len() == b.len(),
            forall|i: int| #![auto] 0 <= i < a.len() ==> add_overflow_safe(a[i], b[i]),
            forall|j: int| #![auto] 0 <= j < idx ==> res[j] == a[j] + b[j],
        decreases a.len() - idx,
    {
        res.push(a[idx] + b[idx]);
        idx = idx + 1;
    }
    
    res
}

spec fn add_overflow_safe(x: i32, y: i32) -> bool {
    -2147483648 <= x + y <= 2147483647
}

}

fn main() {}