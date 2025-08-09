use vstd::prelude::*;

verus! {

fn right_shift(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 65535,
        forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 16,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == ((#[verifier::truncate] (a[i] as u16)) >> (#[verifier::truncate] (b[i] as u16))) as i32,
{
    let mut res = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            res.len() == idx,
            forall|i: int| 0 <= i < idx ==> res[i] == ((#[verifier::truncate] (a[i] as u16)) >> (#[verifier::truncate] (b[i] as u16))) as i32,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases a.len() - idx
    {
        let a_val = a[idx] as u16;
        let b_val = b[idx] as u16;
        let shifted = (a_val >> b_val) as i32;
        res.push(shifted);
        idx += 1;
    }
    
    res
}

}

fn main() {}