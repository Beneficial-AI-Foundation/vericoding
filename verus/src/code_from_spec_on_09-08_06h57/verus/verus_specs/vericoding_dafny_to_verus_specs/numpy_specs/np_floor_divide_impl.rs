use vstd::prelude::*;

verus! {

// SPEC - Floor divide function specification  
#[verifier::external_body]
fn floor_divide(a: Vec<i32>, b: Vec<i32>) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == a[i] / b[i],
{
    let mut res = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == a[j] / b[j],
    {
        res.push(a[i] / b[i]);
        i += 1;
    }
    
    res
}

}

fn main() {}