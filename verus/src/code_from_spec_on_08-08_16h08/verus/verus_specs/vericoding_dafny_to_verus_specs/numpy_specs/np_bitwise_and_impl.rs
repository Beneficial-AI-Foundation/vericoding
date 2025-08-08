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
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == ((#[verifier::truncate] (a[j] as u16)) & (#[verifier::truncate] (b[j] as u16))) as i32,
        decreases a.len() - i
    {
        let a_val = a[i] as u16;
        let b_val = b[i] as u16;
        let and_result = (a_val & b_val) as i32;
        result.push(and_result);
        i += 1;
    }
    
    result
}

}

fn main() {}