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
    let mut result = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result.len() == idx,
            a.len() == b.len(),
            forall|j: int| 0 <= j < a.len() ==> 0 <= #[trigger] a[j] <= 65535,
            forall|j: int| 0 <= j < b.len() ==> #[trigger] b[j] < 16,
            forall|i: int| 0 <= i < idx ==> #[trigger] result[i] == ((#[verifier::truncate] (a[i] as u16)) >> (#[verifier::truncate] (b[i] as u16))) as i32,
        decreases a.len() - idx,
    {
        let val_a = a[idx];
        let val_b = b[idx];
        
        // Use the fact that val_b < 16 to ensure shift amount is valid
        assert(val_b < 16);
        let shift_amount = val_b as u32;
        assert(shift_amount < 16);
        
        let shifted = (#[verifier::truncate] (val_a as u16)) >> shift_amount;
        result.push(shifted as i32);
        idx += 1;
    }
    
    result
}

}

fn main() {}