use vstd::prelude::*;
fn main() {}

verus!{
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let len = v.len();
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            v.len() == old(v).len(),
            forall|j: int| 0 <= j < i ==> v[j] == old(v)[old(v).len() - j - 1],
            forall|j: int| 0 <= j < i ==> v[old(v).len() - j - 1] == old(v)[j],
            forall|j: int| i <= j < old(v).len() - i ==> v[j] == old(v)[j],
    {
        /* code modified by LLM (iteration 1): fixed borrow checker issue by storing both values before any mutable operations */
        let temp1 = v[i];
        let temp2 = v[len - i - 1];
        v.set(i, temp2);
        v.set(len - i - 1, temp1);
        i += 1;
    }
}
}