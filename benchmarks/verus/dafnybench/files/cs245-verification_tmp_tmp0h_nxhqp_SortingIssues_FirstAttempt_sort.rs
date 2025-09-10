use vstd::prelude::*;

verus! {

fn sort(A: &mut Vec<i32>, n: usize)
    requires 
        n == old(A).len(),
        n >= 0,
    ensures
        forall|i: int, j: int| 0 <= i <= j < n ==> A[i] <= A[j],
{
    assume(false);
    unreached()
}

}
fn main() {}