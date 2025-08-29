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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] - b[j],
            forall|k: int| 0 <= k < a.len() ==> 
                a[k] >= i32::MIN + b[k] && a[k] <= i32::MAX + b[k],
        decreases a.len() - i,
    {
        result.push(a[i] - b[i]);
        i += 1;
    }
    result
}

}

fn main() {}