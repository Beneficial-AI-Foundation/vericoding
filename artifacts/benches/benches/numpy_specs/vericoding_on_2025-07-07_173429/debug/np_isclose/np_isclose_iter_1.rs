use vstd::prelude::*;

verus! {

fn np_isclose(a: Vec<i32>, b: Vec<i32>, tol: i32) -> (ret: Vec<bool>)
    requires 
        a.len() > 0,
        a.len() == b.len(),
        tol > 0,
    ensures
        ret.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==>
            ret[i] == (-tol < a[i] - b[i] && a[i] - b[i] < tol),
{
    let mut ret: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            ret.len() == i,
            a.len() == b.len(),
            forall|j: int| #![auto] 0 <= j < i ==>
                ret[j] == (-tol < a[j] - b[j] && a[j] - b[j] < tol),
        decreases a.len() - i,
    {
        let a_val = a[i] as i64;
        let b_val = b[i] as i64;
        let tol_64 = tol as i64;
        
        // Use i64 arithmetic to avoid overflow
        let diff = a_val - b_val;
        let is_close = -tol_64 < diff && diff < tol_64;
        
        proof {
            assert(diff == (a[i as int] - b[i as int]) as i64);
            assert(is_close == (-tol < a[i as int] - b[i as int] && a[i as int] - b[i as int] < tol));
        }
        
        ret.push(is_close);
        i = i + 1;
    }
    
    ret
}

}

fn main() {}