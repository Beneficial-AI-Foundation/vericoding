use vstd::prelude::*;
fn main() {}

verus!{
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let len = v.len();
    let mut i = 0;
    
    while i < len / 2
        invariant
            v.len() == len,
            len == old(v).len(),
            forall|j: int| 0 <= j < i ==> v[j] == old(v)[len - j - 1],
            forall|j: int| len - i <= j < len ==> v[j] == old(v)[len - j - 1],
            forall|j: int| i <= j < len - i ==> v[j] == old(v)[j],
    {
        /* code modified by LLM (iteration 1): store both values in temporaries to avoid borrowing conflicts */
        let temp = v[i];
        let temp2 = v[len - i - 1];
        v.set(i, temp2);
        v.set(len - i - 1, temp);
        i += 1;
    }
}
}