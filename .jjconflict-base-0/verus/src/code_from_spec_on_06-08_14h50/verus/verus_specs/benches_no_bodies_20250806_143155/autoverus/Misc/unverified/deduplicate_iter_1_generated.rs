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
    let mut res = Vec::new();
    let mut seen = HashSet::new();
    
    for i in 0..nums.len()
        invariant
            res@.no_duplicates(),
            res@.to_set().subset_of(nums@.to_set()),
            forall |j: int| 0 <= j < i ==> (#[trigger] nums@[j]) in res@.to_set()
    {
        if !seen.contains(&nums[i]) {
            res.push(nums[i]);
            seen.insert(nums[i]);
        }
    }
    
    res
}
}