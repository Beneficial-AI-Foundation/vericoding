use vstd::prelude::*;

verus! {

fn less_equal(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<bool>)
    requires 
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == (a[i] <= b[i]),
{
    let mut res = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            res.len() == idx,
            forall|i: int| #![auto] 0 <= i < idx ==> res[i] == (a[i] <= b[i]),
            a.len() == b.len(),
        decreases a.len() - idx,
    {
        assert(idx < a.len());
        assert(idx < b.len());
        let cmp_result = a[idx] <= b[idx];
        res.push(cmp_result);
        idx += 1;
    }
    
    res
}

}

fn main() {}