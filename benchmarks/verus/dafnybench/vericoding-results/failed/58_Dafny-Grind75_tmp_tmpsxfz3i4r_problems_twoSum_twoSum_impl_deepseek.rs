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
proof fn lemma_seq_indexing<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.index(i) == s@[i as nat],
{
}

spec fn exists_summing_pair(nums: Seq<int>, target: int) -> bool {
    exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target)
}

proof fn lemma_summing_pair_unique(nums: Seq<int>, target: int, i1: nat, j1: nat, i2: nat, j2: nat)
    requires
        i1 < j1 < nums.len(),
        i2 < j2 < nums.len(),
        summing_pair(i1, j1, nums, target),
        summing_pair(i2, j2, nums, target),
        forall|l: nat, m: nat| l < m < nums.len() && l != i1 && m != j1 ==> !summing_pair(l, m, nums, target),
    ensures
        i1 == i2 && j1 == j2,
{
}

proof fn lemma_summing_pair_commutative(nums: Seq<int>, target: int, i: nat, j: nat)
    requires
        summing_pair(i, j, nums, target),
    ensures
        summing_pair(j, i, nums, target),
{
}

spec fn find_first_summing_pair(nums: Seq<int>, target: int, i: nat, j: nat) -> bool
    recommends
        i < nums.len(),
        j < nums.len(),
{
    if i == j {
        false
    } else if j < i {
        summing_pair(j, i, nums, target)
    } else {
        summing_pair(i, j, nums, target)
    }
}

proof fn lemma_usize_to_nat_conversion(i: usize)
    requires
        i as int >= 0,
    ensures
        i as nat == (i as int) as nat,
{
}

proof fn lemma_nat_bounds(i: nat, len: nat)
    requires
        i < len,
    ensures
        i as int >= 0 && i as int < len as int,
{
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
    let mut j: usize = 1;
    
    while i < nums.len() as usize
        invariant
            0 <= i <= nums.len() as usize,
            0 <= j <= nums.len() as usize,
            i < j || j < nums.len() as usize,
            exists|ii: nat, jj: nat| ii < jj < nums.len() && summing_pair(ii, jj, nums, target),
    {
        while j < nums.len() as usize
            invariant
                0 <= i < nums.len() as usize,
                0 <= j <= nums.len() as usize,
            {
            proof {
                lemma_usize_to_nat_conversion(i);
                lemma_usize_to_nat_conversion(j);
                lemma_nat_bounds(i as nat, nums.len());
                lemma_nat_bounds(j as nat, nums.len());
            }
            if nums.index(i as int) + nums.index(j as int) == target {
                proof {
                    assert(summing_pair(i as nat, j as nat, nums, target)) by {
                        assert(nums.index(i as int) == nums@[i as nat]);
                        assert(nums.index(j as int) == nums@[j as nat]);
                    };
                }
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
        j = i + 1;
    }
    
    proof {
        assert(false); // Contradiction with precondition
    }
    (0, 0)
}
// </vc-code>

fn main() {
}

}