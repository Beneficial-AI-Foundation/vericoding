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
    let mut ret: Vec<bool> = Vec::new();
    let n = a.len();
    let mut idx: usize = 0;
    let neg_tol = -tol;  // Compute once to avoid repeated negation
    
    while idx < n
        invariant
            n == a.len(),
            n == b.len(),
            0 <= idx <= n,
            ret.len() == idx,
            tol > 0,
            tol < i32::MAX / 2,
            neg_tol == -tol,
            forall|i: int| 0 <= i < n ==> 
                a[i] > i32::MIN / 2 && a[i] < i32::MAX / 2,
            forall|i: int| 0 <= i < n ==> 
                b[i] > i32::MIN / 2 && b[i] < i32::MAX / 2,
            forall|j: int| 0 <= j < idx ==> 
                ret[j] == (neg_tol < a[j] - b[j] < tol),
        decreases n - idx,
    {
        let a_val = a[idx];
        let b_val = b[idx];
        
        // With our bounds, this arithmetic is safe
        let diff = a_val - b_val;
        let result = (neg_tol < diff) && (diff < tol);
        
        proof {
            assert(neg_tol == -tol);
            assert((neg_tol < diff) == (-tol < diff));
        }
        
        ret.push(result);
        idx = idx + 1;
    }
    
    ret
}

}

fn main() {}