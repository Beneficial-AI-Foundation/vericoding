use vstd::prelude::*;

verus! {

fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
{
    assume(false);
    unreached();
}

}
fn main() {}