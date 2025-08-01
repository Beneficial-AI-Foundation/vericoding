use vstd::prelude::*;

verus! {

fn myfun1(x: &Vec<i32>) -> (max_index: usize)
    // pre-conditions-start
    requires
        x.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!


fn main() {}