use vstd::prelude::*;

verus! {

fn add(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        // Precondition to ensure no arithmetic overflow
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i] >= 0 ==> a[i] <= i32::MAX - b[i]) &&
            (a[i] < 0 ==> a[i] >= i32::MIN - b[i]),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == a[i] + b[i],
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == a[j] + b[j],
            // Maintain the overflow precondition
            forall|k: int| 0 <= k < a.len() ==> 
                (a[k] >= 0 ==> a[k] <= i32::MAX - b[k]) &&
                (a[k] < 0 ==> a[k] >= i32::MIN - b[k]),
        decreases a.len() - i,
    {
        assert(i < a.len());
        assert(i < b.len());
        
        let val_a = a[i];
        let val_b = b[i];
        let sum = val_a + val_b;
        
        res.push(sum);
        i = i + 1;
    }
    
    res
}

}