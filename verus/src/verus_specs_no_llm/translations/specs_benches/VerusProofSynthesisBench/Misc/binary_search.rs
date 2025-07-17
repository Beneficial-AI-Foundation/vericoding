use vstd::prelude::*;

verus!{
fn binary_search(v: &Vec<u64>, k: u64) -> (result:usize)
    // pre-conditions-start
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],
    // pre-conditions-end
    // post-conditions-start
    ensures
        result < v.len(),
        k == v[result as int],
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}
}

fn main() {}
