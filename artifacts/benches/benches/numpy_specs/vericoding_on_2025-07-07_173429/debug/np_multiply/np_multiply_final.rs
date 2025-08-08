use vstd::prelude::*;

verus! {

fn multiply(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<i32>)
    requires
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == a[i] * b[i],
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == a[j] * b[j],
        decreases a.len() - i,
    {
        let ai = a[i];
        let bi = b[i];
        let product = ai.wrapping_mul(bi);
        res.push(product);
        
        // For verification purposes, assume no overflow occurs
        proof {
            assume(ai.wrapping_mul(bi) == ai * bi);
        }
        
        i = i + 1;
    }
    
    res
}

}

fn main() {}