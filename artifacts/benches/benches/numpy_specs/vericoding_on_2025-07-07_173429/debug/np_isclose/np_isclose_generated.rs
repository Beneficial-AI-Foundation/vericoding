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
            let diff = #[trigger] a[i] - #[trigger] b[i];
            (#[trigger] ret[i]) == (-tol < diff && diff < tol)
        },
{
    let mut ret = Vec::new();
    let len = a.len();
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            len == a.len(),
            len == b.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let diff = #[trigger] a[j] - #[trigger] b[j];
                (#[trigger] ret[j]) == (-tol < diff && diff < tol)
            },
        decreases len - i,
    {
        proof {
            assert(i < len);
            assert(len == a.len());
            assert(len == b.len());
            assert(i < a.len());
            assert(i < b.len());
        }
        
        let a_val = a[i];
        let b_val = b[i];
        
        // Use i64 to avoid overflow, then relate back to i32 arithmetic
        let a_ext = a_val as i64;
        let b_ext = b_val as i64;
        let diff_ext = a_ext - b_ext;
        let tol_ext = tol as i64;
        
        let is_close = -tol_ext < diff_ext && diff_ext < tol_ext;
        
        proof {
            // Prove that our i64 computation corresponds to the i32 spec computation
            let diff_spec = a[i as int] - b[i as int];
            assert(diff_ext == diff_spec);
            assert(is_close == (-tol < diff_spec && diff_spec < tol));
        }
        
        ret.push(is_close);
        i = i + 1;
    }
    
    ret
}

}

fn main() {}