#[allow(unused_imports)]
use vstd::prelude::*;
use std::collections::HashSet;
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
    /* code modified by LLM (iteration 1): added HashSet import and initialized HashSet */
    let mut seen = HashSet::new();
    
    /* code modified by LLM (iteration 1): fixed syntax error with 'in' operator, changed to use contains method and added proof block for verification */
    for i in 0..nums.len()
        invariant
            res@.no_duplicates(),
            res@.to_set().subset_of(nums@.to_set()),
            forall |j: int| 0 <= j < i ==> res@.to_set().contains(nums@[j]),
            forall |x: i32| res@.to_set().contains(x) ==> nums@.to_set().contains(x),
            forall |j: int| 0 <= j < i && nums@.to_set().contains(nums@[j]) ==> res@.to_set().contains(nums@[j])
    {
        if !seen.contains(&nums[i]) {
            res.push(nums[i]);
            seen.insert(nums[i]);
            
            proof {
                assert(nums@.to_set().contains(nums@[i as int]));
                assert(res@.to_set().contains(nums@[i as int]));
            }
        }
    }
    
    /* code modified by LLM (iteration 1): added proof block to establish the final postcondition */
    proof {
        assert(forall |x: i32| nums@.to_set().contains(x) ==> res@.to_set().contains(x));
        assert(forall |x: i32| res@.to_set().contains(x) ==> nums@.to_set().contains(x));
    }
    
    res
}
}