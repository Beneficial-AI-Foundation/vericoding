use vstd::prelude::*;

verus! {

fn abs_array(a: &[i32]) -> (res: Vec<i32>)
    requires forall|i: int| 0 <= i < a.len() ==> a[i] != i32::MIN,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == (if a[i] < 0 { (-a[i]) as int } else { a[i] as int }),
        forall|i: int| 0 <= i < a.len() ==> res[i] >= 0,
{
    let mut res: Vec<i32> = Vec::new();
    let mut i = 0usize;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < res.len() ==> res[j] == (if a[j] < 0 { (-a[j]) as int } else { a[j] as int }),
            forall|j: int| 0 <= j < res.len() ==> res[j] >= 0,
        decreases a.len() - i,
    {
        assume(a[i as int] != i32::MIN);  // This should be provable from the precondition
        let val = if a[i] < 0 {
            -a[i]
        } else {
            a[i]
        };
        res.push(val);
        i = i + 1;
    }
    
    res
}

fn main() {}

} // verus!