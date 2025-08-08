use vstd::prelude::*;

verus! {

fn less(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires 
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res@[i] == (a@[i] < b@[i]),
{
    let len = a.len();
    let mut result: Vec<bool> = Vec::with_capacity(len);
    let mut idx: usize = 0;
    
    while idx < len
        invariant
            idx <= len,
            len == a.len(),
            len == b.len(),
            result.len() == idx,
            forall|j: int| #![auto] 0 <= j < idx ==> result@[j] == (a@[j] < b@[j]),
        decreases len - idx,
    {
        let less_than = a[idx] < b[idx];
        result.push(less_than);
        idx += 1;
    }
    
    result
}

}

fn main() {}