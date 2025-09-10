use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

fn top_k_frequent(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
{
    assume(false);
    unreached();
}

}
fn main() {}