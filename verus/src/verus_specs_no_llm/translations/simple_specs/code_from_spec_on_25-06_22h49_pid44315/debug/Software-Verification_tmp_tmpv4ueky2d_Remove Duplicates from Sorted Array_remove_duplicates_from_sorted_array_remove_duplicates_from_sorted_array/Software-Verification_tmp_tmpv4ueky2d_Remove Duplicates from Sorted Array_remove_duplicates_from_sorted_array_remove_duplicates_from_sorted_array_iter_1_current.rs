use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_sorted(nums: Seq<int>) -> bool {
    forall i, j :: 0 <= i < j < nums.len() ==> nums.spec_index(i) <= nums.spec_index(j)
}

spec fn is_sorted_and_distinct(nums: Seq<int>) -> bool {
    forall i, j :: 0 <= i < j < nums.len() ==> nums.spec_index(i) < nums.spec_index(j)
}

fn remove_duplicates_from_sorted_array(nums: Seq<int>) -> (result: Seq<int>)
    requires
        is_sorted(nums),
        1 <= nums.len() <= 30000,
        forall i :: 0 <= i < nums.len() ==> -100 <= nums.spec_index(i) <= 100
    ensures
        is_sorted_and_distinct(result),
        forall i :: i in nums <==> i in result
{
    let mut result = Seq::empty();
    let mut idx = 0;
    
    while idx < nums.len()
        invariant
            0 <= idx <= nums.len(),
            is_sorted_and_distinct(result),
            forall i :: i in result ==> i in nums,
            forall i :: 0 <= i < idx ==> (nums.spec_index(i) in result),
            forall i :: i in result ==> exists j :: 0 <= j < idx && nums.spec_index(j) == i
    {
        let current = nums.spec_index(idx);
        
        if result.len() == 0 || result.spec_index(result.len() - 1) != current {
            result = result.push(current);
        }
        
        idx = idx + 1;
    }
    
    result
}

}