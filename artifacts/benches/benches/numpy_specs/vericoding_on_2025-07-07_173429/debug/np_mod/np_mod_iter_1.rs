use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn safe_mod(a: i32, b: i32) -> (result: i32)
    requires b != 0
    ensures result == a % b
{
    a % b
}

fn mod_arrays(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] % b[i],
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == a[j] % b[j],
            forall|k: int| 0 <= k < b.len() ==> b[k] != 0,
        decreases a.len() - i,
    {
        proof {
            assert(i < b.len());
            assert(b[i as int] != 0);
        }
        
        let result = safe_mod(a[i], b[i]);
        res.push(result);
        i = i + 1;
    }
    
    res
}

}