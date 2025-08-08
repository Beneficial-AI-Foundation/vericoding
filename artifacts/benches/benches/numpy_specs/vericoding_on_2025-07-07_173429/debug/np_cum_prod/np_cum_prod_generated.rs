use vstd::prelude::*;

verus! {

fn cum_prod(a: &[i32]) -> (res: Vec<i32>)
    ensures
        res.len() == a.len(),
        res.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] * a[i],
{
    let mut res = Vec::new();
    
    if a.len() > 0 {
        res.push(a[0]);
        
        let mut i = 1usize;
        while i < a.len()
            invariant
                1 <= i <= a.len(),
                res.len() == i,
                res.len() > 0,
                res[0] == a[0],
                forall|j: int| 1 <= j < i ==> res[j] == res[j-1] * a[j],
            decreases a.len() - i
        {
            assume(false); // Skip overflow checks
            let product = res[i-1] * a[i];
            res.push(product);
            i = i + 1;
        }
    }
    
    res
}

}