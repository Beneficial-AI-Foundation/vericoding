use vstd::prelude::*;

verus! {

fn bitwise_xor(a: &[u32], b: &[u32]) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 65535,
        forall|i: int| 0 <= i < b.len() ==> 0 <= #[trigger] b[i] <= 65535,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == (#[verifier::truncate] (a[i] as u16) ^ #[verifier::truncate] (b[i] as u16)) as u32,
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == (#[verifier::truncate] (a[j] as u16) ^ #[verifier::truncate] (b[j] as u16)) as u32,
        decreases a.len() - i,
    {
        res.push((#[verifier::truncate] (a[i] as u16) ^ #[verifier::truncate] (b[i] as u16)) as u32);
        i = i + 1;
    }
    res
}

}

fn main() {
}