use vstd::prelude::*;

fn main() {}
verus! {

fn append(v: &Vec<u64>, elem: u64) -> (c: Vec<u64>)
    requires
        v.len() <= 100,
    ensures
        c@.len() == v@.len() + 1,
        forall|i: int| (0 <= i && i < v.len()) ==> c[i] == v[i],
        c@.last() == elem,
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!
