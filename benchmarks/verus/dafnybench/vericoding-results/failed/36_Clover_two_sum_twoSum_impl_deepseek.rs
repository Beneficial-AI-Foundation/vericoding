use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_index_valid<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] is T,
{
}

proof fn lemma_unique_solution(nums: Seq<i32>, target: i32, i: int, j: int, k: int, l: int)
    requires
        0 <= i < j < nums.len(),
        0 <= k < l < nums.len(),
        nums[i] + nums[j] == target,
        nums[k] + nums[l] == target,
    ensures
        i == k && j == l || i != k || j != l,
{
}

spec fn find_first_solution(nums: Seq<i32>, target: i32) -> (i: int, j: int)
    recommends
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
        forall|jj: int| #![trigger nums[jj]] i < jj < j ==> nums[i] + nums[jj] != target,
{
    let mut i_candidate: int = 0;
    
    while i_candidate < nums.len() as int - 1
        invariant
            0 <= i_candidate <= nums.len() as int - 1,
            forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < i_candidate && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
    {
        let mut j_candidate: int = i_candidate + 1;
        
        while j_candidate < nums.len() as int
            invariant
                i_candidate < j_candidate <= nums.len() as int,
                forall|jj: int| #![trigger nums[jj]] i_candidate < jj < j_candidate ==> nums[i_candidate] + nums[jj] != target,
        {
            if nums[i_candidate] + nums[j_candidate] == target {
                return (i_candidate, j_candidate);
            }
            j_candidate += 1;
        }
        i_candidate += 1;
    }
    
    (i_candidate, 0)
}
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: &[i32], target: i32) -> (result: (usize, usize))
    requires 
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures 
        0 <= result.0 < result.1 < nums.len() && nums[result.0 as int] + nums[result.1 as int] == target
        && forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < result.0 && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target
        && forall|jj: int| #![trigger nums[jj]] result.0 < jj < result.1 ==> nums[result.0 as int] + nums[jj] != target,
// </vc-spec>
// <vc-code>
{
    let n = nums.len() as int;
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    proof {
        let (spec_i, spec_j) = find_first_solution(nums@, target);
        i = spec_i as usize;
        j = spec_j as usize;
    }
    
    proof {
        assert(0 <= i as int < j as int < n);
        assert(nums@[i as int] + nums@[j as int] == target);
        assert(forall|ii: int, jj: int| #![trigger nums@[ii], nums@[jj]] (0 <= ii < i as int && ii < jj < n) ==> nums@[ii] + nums@[jj] != target);
        assert(forall|jj: int| #![trigger nums@[jj]] i as int < jj < j as int ==> nums@[i as int] + nums@[jj] != target);
    }
    
    (i, j)
}
// </vc-code>

fn main() {}

}