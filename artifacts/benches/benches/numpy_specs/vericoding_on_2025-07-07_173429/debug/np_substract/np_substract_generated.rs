use vstd::prelude::*;

verus! {

fn subtract(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        // Precondition to ensure no overflow
        forall|i: int| 0 <= i < a.len() ==> 
            -2147483648 <= #[trigger] a[i] - b[i] <= 2147483647,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] - b[i],
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|k: int| 0 <= k < a.len() ==> 
                -2147483648 <= #[trigger] a[k] - b[k] <= 2147483647,
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == a[j] - b[j],
        decreases a.len() - i,
    {
        res.push(a[i] - b[i]);
        i = i + 1;
    }
    
    res
}

}

fn main() {}