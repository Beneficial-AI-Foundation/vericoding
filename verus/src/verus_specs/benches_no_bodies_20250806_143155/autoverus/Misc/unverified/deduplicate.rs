#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}


fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
ensures
    res@.no_duplicates(),
    nums@.to_set().ext_equal(res@.to_set())
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}
}
