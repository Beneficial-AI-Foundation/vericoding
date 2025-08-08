use vstd::prelude::*;

verus! {

fn abs_array(a: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() <= usize::MAX,
        forall|idx: int| 0 <= idx < a.len() ==> a[idx] != i32::MIN,
    ensures
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == (if a[i] < 0 { -a[i] as int } else { a[i] as int }),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] >= 0,
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            forall|idx: int| 0 <= idx < a.len() ==> a[idx] != i32::MIN,
            forall|j: int| #![auto] 0 <= j < res.len() ==> res[j] == (if a[j] < 0 { -a[j] as int } else { a[j] as int }),
            forall|j: int| #![auto] 0 <= j < res.len() ==> res[j] >= 0,
        decreases a.len() - i,
    {
        let elem = a[i];
        if elem < 0 {
            assert(elem != i32::MIN);
            let neg_elem = -elem;
            res.push(neg_elem);
        } else {
            res.push(elem);
        }
        i = i + 1;
    }
    
    res
}

fn main() {}

}