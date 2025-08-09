use vstd::prelude::*;

verus! {

fn np_isclose(a: &Vec<i32>, b: &Vec<i32>, tol: i32) -> (ret: Vec<bool>)
    requires
        a.len() > 0,
        a.len() == b.len(),
        tol > 0,
        tol < i32::MAX / 2,  // Ensure we can negate safely
        // Simple bounds to avoid overflow
        forall|i: int| 0 <= i < a.len() ==> 
            #[trigger] a[i] > i32::MIN / 2 && #[trigger] a[i] < i32::MAX / 2,
        forall|i: int| 0 <= i < b.len() ==> 
            #[trigger] b[i] > i32::MIN / 2 && #[trigger] b[i] < i32::MAX / 2,
    ensures
        ret.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            ret[i] == (-tol < a[i] - b[i] < tol),
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> 
                result[i] == (-tol < a[i] - b[i] < tol),
        decreases a.len() - idx
    {
        let diff = a[idx] - b[idx];
        let is_close = -tol < diff && diff < tol;
        result.push(is_close);
        idx += 1;
    }
    
    result
}

}

fn main() {}