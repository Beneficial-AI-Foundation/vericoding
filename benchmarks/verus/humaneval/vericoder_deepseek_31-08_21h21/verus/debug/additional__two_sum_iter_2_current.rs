use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_indexing<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s[i],
{
}

spec fn find_pair(s: Seq<i32>, target: i32) -> (i: int, j: int)
    recommends
        s.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < s.len() && s[i] + s[j] == target,
    ensures
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j,
        s[i] + s[j] == target,
{
    choose|i: int, j: int| 0 <= i < j < s.len() && s[i] + s[j] == target
}

proof fn lemma_find_pair_exists(nums: Seq<i32>, target: i32)
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        find_pair(nums, target).0 != find_pair(nums, target).1,
        nums[find_pair(nums, target).0] + nums[find_pair(nums, target).1] == target,
{
    let (i, j) = find_pair(nums, target);
    assert(i != j);
    assert(nums[i] + nums[j] == target);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    // pre-conditions-start
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    proof {
        lemma_find_pair_exists(nums@, target);
    }
    let (i_spec, j_spec) = find_pair(nums@, target);
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|k: int, l: int| 0 <= k < i && k < l < n ==> nums[k] + nums[l] != target,
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                j <= n,
                forall|l: int| i < l < j ==> nums[i] + nums[l] != target,
        {
            if nums[i] + nums[j] == target {
                proof {
                    assert(nums@[i as int] + nums@[j as int] == target);
                }
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    
    proof {
        assert(i_spec < j_spec);
        assert(nums@[i_spec] + nums@[j_spec] == target);
        assert(0 <= i_spec < n as int);
        assert(0 <= j_spec < n as int);
        assert(false); // Contradiction with pre-condition
    }
    (0, 0)
}
// </vc-code>

fn main() {}
}