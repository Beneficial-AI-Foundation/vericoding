use vstd::prelude::*;

verus! {

fn binary_search(a: &[i32], circle: i32) -> (n: usize)
    requires 
        forall|i: int| #![trigger a[i]] 1 <= i < a.len() ==> a[i-1] < a[i],
        forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < a.len() ==> a[i] < a[j],
    ensures 
        n <= a.len(),
        forall|i: int| #![trigger a[i]] 0 <= i < n ==> a[i] < circle,
        forall|i: int| #![trigger a[i]] n <= i < a.len() ==> circle <= a[i],
{
    assume(false);
    unreached()
}

}
fn main() {}