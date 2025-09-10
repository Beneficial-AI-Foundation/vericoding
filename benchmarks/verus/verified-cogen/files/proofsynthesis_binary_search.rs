use vstd::prelude::*;

verus!{

fn binary_search(v: &Vec<u64>, k: u64) -> (result:usize)

    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],

    ensures
        result < v.len(),
        k == v[result as int],
{
    assume(false);
    unreached();
}

}
fn main() {}