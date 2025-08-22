use vstd::prelude::*;

fn main() {}

verus! {

fn two_sum(nums: &Vec<u32>, target: u32) -> (r: (usize, usize))
    requires
        nums.len() > 1,
        forall|ii: int, jj: int|
            ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                < 256,
        exists|i: int, j: int| (0 <= i && i < j && j < nums.len()) && nums[i] + nums[j] == target,
    ensures
        (0 <= r.0 && r.0 < r.1 && r.1 < nums.len()) && nums[r.0 as int] + nums[r.1 as int]
            == target,
        forall|ii: int, jj: int|
            ((0 <= ii && ii < r.0 && ii < jj && jj < nums.len()) || (ii == r.0 && ii < jj && jj
                < r.1)) ==> nums[ii] + nums[jj] != target,
{
    let mut i = 0;
    while i < nums.len() - 1
        invariant
            0 <= i < nums.len(),
            forall|ii: int, jj: int|
                ((0 <= ii && ii < i && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj] != target,
            exists|ii: int, jj: int| (i <= ii && ii < jj && jj < nums.len()) && nums[ii] + nums[jj] == target,
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len() - 1,
                i + 1 <= j <= nums.len(),
                forall|ii: int, jj: int|
                    ((0 <= ii && ii < i && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj] != target,
                forall|jj: int|
                    ((i + 1 <= jj && jj < j)) ==> nums[i as int] + nums[jj] != target,
                exists|ii: int, jj: int| (i <= ii && ii < jj && jj < nums.len()) && nums[ii] + nums[jj] == target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): Replaced unreachable!() with proof that this point is unreachable based on preconditions */
    proof {
        // We know from the precondition that a solution exists
        // and our loop invariant guarantees we haven't skipped any valid pairs
        // This assertion should help the verifier understand this is unreachable
        assert(false);
    }
    (0, 1) // This line will never be reached, but needed for compilation
}

} // verus!