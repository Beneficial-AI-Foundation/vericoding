use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn abs(a: &Vec<i32>) -> (res: Vec<i32>)
    requires 
        forall|i: int| 0 <= i < a.len() ==> a[i] != i32::MIN,  // Prevent negation overflow
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == (if a[i] < 0 { -a[i] as int } else { a[i] as int }),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] >= 0,
{
    let mut res: Vec<i32> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == (if a[j] < 0 { -a[j] as int } else { a[j] as int }),
            forall|j: int| #![auto] 0 <= j < i ==> res[j] >= 0,
        decreases a.len() - i,
    {
        if a[i] < 0 {
            res.push(-a[i]);
        } else {
            res.push(a[i]);
        }
        i = i + 1;
    }
    res
}

fn main() {}

}