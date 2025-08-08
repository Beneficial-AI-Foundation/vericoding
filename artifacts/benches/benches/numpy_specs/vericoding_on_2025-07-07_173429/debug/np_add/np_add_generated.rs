use vstd::prelude::*;

verus! {

fn add(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] + b[i],
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == a[j] + b[j],
        decreases a.len() - i,
    {
        assume(a[i as int].checked_add(b[i as int]).is_some());
        res.push(a[i] + b[i]);
        i = i + 1;
    }
    
    res
}

}

fn main() {}