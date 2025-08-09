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
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> #[trigger] result[i] == ((#[verifier::truncate] (a[i] as u16)) & (#[verifier::truncate] (b[i] as u16))) as i32,
        decreases a.len() - idx
    {
        let a_val = a[idx] as u16;
        let b_val = b[idx] as u16;
        let bitwise_result = (a_val & b_val) as i32;
        result.push(bitwise_result);
        idx += 1;
    }
    
    result
}

}

fn main() {}