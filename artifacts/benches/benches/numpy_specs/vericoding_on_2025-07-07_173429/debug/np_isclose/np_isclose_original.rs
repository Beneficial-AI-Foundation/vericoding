use vstd::prelude::*;

verus! {

fn np_isclose(a: &[i32], b: &[i32], tol: i32) -> (ret: Vec<bool>)
    requires
        a.len() > 0,
        a.len() == b.len(),
        tol > 0,
    ensures
        ret.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            if -tol < a[i] - b[i] < tol {
                ret[i]
            } else {
                !ret[i]
            }
        },
{
    let mut result: Vec<bool> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            a.len() == b.len(),
            result.len() == idx,
            forall|j: int| 0 <= j < idx ==> {
                if -tol < a[j] - b[j] < tol {
                    result[j]
                } else {
                    !result[j]
                }
            },
        decreases a.len() - idx,
    {
        // Use i64 to avoid overflow issues in the comparison
        let val_a: i64 = a[idx] as i64;
        let val_b: i64 = b[idx] as i64;
        let tol_64: i64 = tol as i64;
        
        let diff = val_a - val_b;
        let is_close = (-tol_64 < diff) && (diff < tol_64);
        
        result.push(is_close);
        idx = idx + 1;
    }
    
    result
}

fn main() {}

}