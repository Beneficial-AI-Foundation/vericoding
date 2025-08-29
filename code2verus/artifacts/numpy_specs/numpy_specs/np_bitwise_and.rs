use vstd::prelude::*;

verus! {

fn bitwise_and(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0 && #[trigger] a[i] <= 65535 && #[trigger] b[i] >= 0 && #[trigger] b[i] <= 65535,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == ((#[verifier::truncate] (a[i] as u16)) & (#[verifier::truncate] (b[i] as u16))) as i32,
{
    let mut result = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result.len() == idx,
            a.len() == b.len(),
            forall|i: int| 0 <= i < idx ==> #[trigger] result[i] == ((#[verifier::truncate] (a[i] as u16)) & (#[verifier::truncate] (b[i] as u16))) as i32,
        decreases a.len() - idx,
    {
        assert(idx < a.len());
        assert(a.len() == b.len());
        assert(idx < b.len());
        let val = ((#[verifier::truncate] (a[idx] as u16)) & (#[verifier::truncate] (b[idx] as u16))) as i32;
        result.push(val);
        idx += 1;
    }
    
    result
}

}

fn main() {}