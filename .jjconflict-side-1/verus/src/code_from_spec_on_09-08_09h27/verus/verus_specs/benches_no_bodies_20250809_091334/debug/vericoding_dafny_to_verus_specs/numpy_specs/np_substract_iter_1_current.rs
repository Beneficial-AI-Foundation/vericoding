use vstd::prelude::*;

verus! {

fn subtract(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        // Add requirement to prevent overflow
        forall|i: int| 0 <= i < a.len() ==> 
            a[i] >= i32::MIN + b[i] && a[i] <= i32::MAX + b[i],
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] - b[i],
{
    let mut result: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == a[i] - b[i],
    {
        let diff = a[idx] - b[idx];
        result.push(diff);
        idx += 1;
    }
    
    result
}

}

fn main() {}