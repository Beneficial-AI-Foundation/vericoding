use vstd::prelude::*;

verus! {

fn bitwise_xor(a: &Vec<u32>, b: &Vec<u32>) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 65535,
        forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] <= 65535,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == (a[i] as u16 ^ b[i] as u16) as u32,
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == (a[j] as u16 ^ b[j] as u16) as u32,
        decreases a.len() - i,
    {
        assert(i < b.len()) by {
            assert(a.len() == b.len());
        };
        let xor_result = (a[i] as u16 ^ b[i] as u16) as u32;
        res.push(xor_result);
        i += 1;
    }
    
    res
}

}

fn main() {}