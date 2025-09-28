use vstd::prelude::*;

verus! {

spec fn summing_pair(i: nat, j: nat, nums: Seq<int>, target: int) -> bool
    recommends 
        i < nums.len(),
        j < nums.len(),
{
    i != j && nums[i as int] + nums[j as int] == target
}

// <vc-helpers>
fn get_nums_at_idx(nums: Seq<int>, i: usize) -> (res: int)
    requires i < nums.len()
    ensures res == nums.index(i as nat)
{
    nums.index(i as nat)
}
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: Seq<int>, target: int) -> (pair: (usize, usize))
    requires exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
    ensures 
        0 <= pair.0 < nums.len() && 
        0 <= pair.1 < nums.len() && 
        summing_pair(pair.0 as nat, pair.1 as nat, nums, target)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < nums.len() {
        invariant 
            0 <= i,
            i <= nums.len(),
            // This loop iterates through 'i', and for each 'i', the inner loop iterates through 'j'.
            // The precondition states that a unique summing pair exists.
            // As we increment 'i', we know that no solutions for earlier 'i' values
            // combined with any 'j' values (either before or after the current 'i') satisfy the condition.
            // This means we have not found the pair yet for any earlier 'i'.
            forall |l: nat, m: nat| 
                #![trigger summing_pair(l, m, nums, target)]
                (l < i as nat || (l == i as nat && m < nums.len()))  // Check if (l, m) is processed before (i, j)
                && (l < m)                                         // Ensure l < m as per precondition
                ==> !summing_pair(l, m, nums, target),
        ;
        let mut j: usize = 0;
        while j < nums.len() {
            invariant 
                0 <= i,
                i < nums.len(),
                0 <= j,
                j <= nums.len(),
                // This preserves the invariant from the outer loop.
                forall |l: nat, m: nat| 
                    #![trigger summing_pair(l, m, nums, target)]
                    (l < i as nat || (l == i as nat && m < j as nat))
                    && (l < m)
                    ==> !summing_pair(l, m, nums, target),
            ;
            if i != j && nums.index(i as nat) + nums.index(j as nat) == target {
                // If we find the pair, prove it's the required one by showing that all previous
                // pairs (l, m) with l < m did not sum to target.
                // The outer invariant already proves that for l < i, and for l = i and m < j.
                // The precondition guarantees uniqueness and existence.
                // Since this is the first (i, j) pair found in lexicographical order, it must be the correct one.
                proof {
                    assert(summing_pair(i as nat, j as nat, nums, target));
                    // The precondition guarantees existence and uniqueness.
                    // The loops check pairs in increasing lexicographical order (i, j).
                    // If we reach this point, (i, j) must be the unique pair.
                    assert(exists|x: nat, y: nat| x < y < nums.len() && summing_pair(x, y, nums, target));
                    assert(forall|l: nat, m: nat| l < m < nums.len() && l != i as nat && m != j as nat ==> !summing_pair(l, m, nums, target));
                }
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    // This part should be unreachable given the `requires` clause.
    // However, Rust requires a return value.
    // We can return an arbitrary pair, as the pre-condition guarantees a solution exists.
    // We choose (0,0) as an arbitrary valid pair.
    (0, 0)
}
// </vc-code>

fn main() {
}

}