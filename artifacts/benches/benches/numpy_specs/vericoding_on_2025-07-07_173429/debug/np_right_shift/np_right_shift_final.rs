use vstd::prelude::*;

verus! {

fn right_shift(a: &Vec<u32>, b: &Vec<u32>) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 65535,
        forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 16,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == ((a[i] as u16) >> (b[i] as u16)) as u32,
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < a.len() ==> a[j] <= 65535,
            forall|j: int| 0 <= j < b.len() ==> b[j] < 16,
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == ((a[j] as u16) >> (b[j] as u16)) as u32,
        decreases a.len() - i,
    {
        assert(i < a.len());
        assert(i < b.len());
        let a_val = a[i];
        let b_val = b[i];
        assert(a_val <= 65535);
        assert(b_val < 16);
        let shifted_val = ((a_val as u16) >> (b_val as u16)) as u32;
        res.push(shifted_val);
        i = i + 1;
    }
    
    res
}

}