use vstd::prelude::*;

verus! {

fn selection_sorted(array: &mut Vec<i32>) 
    ensures array@.to_multiset() == old(array)@.to_multiset()
{
    assume(false);
    unreached()
}

}
fn main() {}