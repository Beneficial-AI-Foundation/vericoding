use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TwoSum(nums: Vec<int>, target: int) -> (r: (int, int))
    ensures
        (r.0 >= 0 && r.1 >= 0) ==> (0 <= r.0 < r.1 < nums.len() && 
            nums.spec_index(r.0) + nums.spec_index(r.1) == target &&
            forall|i: int, j: int| 0 <= i < j < nums.len() && (i < r.0 || (i == r.0 && j < r.1)) ==> nums.spec_index(i) + nums.spec_index(j) != target),
        (r.0 == -1 && r.1 == -1) <==> forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums.spec_index(i) + nums.spec_index(j) != target
{
    let n = nums.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|ii: int, jj: int| 0 <= ii < jj < nums.len() && ii < i ==> nums.spec_index(ii) + nums.spec_index(jj) != target
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i + 1 <= j <= n,
                i < n,
                0 <= i < n,
                forall|jj: int| (i + 1) <= jj < j ==> nums.spec_index(i as int) + nums.spec_index(jj) != target,
                forall|ii: int, jj: int| 0 <= ii < jj < nums.len() && ii < i ==> nums.spec_index(ii) + nums.spec_index(jj) != target
        {
            if nums[i] + nums[j] == target {
                // Prove the postcondition holds
                assert(nums.spec_index(i as int) + nums.spec_index(j as int) == target);
                assert(0 <= i as int < j as int < nums.len());
                
                // Prove no earlier pair works
                assert(forall|ii: int, jj: int| 0 <= ii < jj < nums.len() && (ii < i as int || (ii == i as int && jj < j as int)) ==> nums.spec_index(ii) + nums.spec_index(jj) != target) by {
                    // From the loop invariants, we know:
                    // 1. No pairs with first index < i work (outer loop invariant)
                    // 2. No pairs with first index = i and second index in [i+1, j) work (inner loop invariant)
                    
                    // For any pair (ii, jj) with ii < i as int
                    assert(forall|ii: int, jj: int| 0 <= ii < jj < nums.len() && ii < i as int ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
                    
                    // For any pair (ii, jj) with ii == i as int and jj < j as int
                    // We need jj >= i+1 for it to be a valid pair, and jj < j
                    assert(forall|jj: int| 0 <= jj < nums.len() && jj > i as int && jj < j as int ==> nums.spec_index(i as int) + nums.spec_index(jj) != target);
                };
                
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    // Prove no valid pair exists
    assert(forall|ii: int, jj: int| 0 <= ii < jj < nums.len() ==> nums.spec_index(ii) + nums.spec_index(jj) != target) by {
        // At this point i == n, so the outer loop invariant covers all possible first indices
        assert(i == n);
        // The invariant states that for all ii < i (which is now n), no pair works
        // Since any valid pair (ii, jj) with 0 <= ii < jj < nums.len() has ii < nums.len() = n = i
        // Therefore all pairs are covered by the invariant
    };
    
    return (-1, -1);
}

}