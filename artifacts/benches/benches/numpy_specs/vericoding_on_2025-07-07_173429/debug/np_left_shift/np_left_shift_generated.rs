use vstd::prelude::*;

verus! {

fn left_shift(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        a.len() < usize::MAX,
        forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 16,
        forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] < 65536,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            #[trigger] res[i] == ((a[i] as u16) << (b[i] as u16)) as i32,
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] < 65536,
            forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] < 16,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] res[j] == ((a[j] as u16) << (b[j] as u16)) as i32,
        decreases a.len() - i,
    {
        let a_val = a[i];
        let b_val = b[i];
        let shifted_val = ((a_val as u16) << (b_val as u16)) as i32;
        res.push(shifted_val);
        i = i + 1;
    }
    
    res
}

}

fn main() {}