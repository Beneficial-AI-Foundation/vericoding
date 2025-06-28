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
            forall|ii: int, jj: int| 0 <= ii < jj < nums.len() && ii < i as int ==> nums.spec_index(ii) + nums.spec_index(jj) != target
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i + 1 <= j <= n,
                i < n,
                0 <= i < n,
                forall|jj: int| (i as int) < jj < (j as int) ==> nums.spec_index(i as int) + nums.spec_index(jj) != target,
                forall|ii: int, jj: int| 0 <= ii < jj < nums.len() && ii < i as int ==> nums.spec_index(ii) + nums.spec_index(jj) != target
        {
            if nums[i] + nums[j] == target {
                // Establish the postcondition
                assert(nums.spec_index(i as int) + nums.spec_index(j as int) == target);
                assert(0 <= i as int < j as int < nums.len());
                
                // Prove the uniqueness property
                assert(forall|ii: int, jj: int| 0 <= ii < jj < nums.len() && (ii < i as int || (ii == i as int && jj < j as int)) ==> nums.spec_index(ii) + nums.spec_index(jj) != target) by {
                    forall|ii: int, jj: int| 0 <= ii < jj < nums.len() && (ii < i as int || (ii == i as int && jj < j as int)) implies nums.spec_index(ii) + nums.spec_index(jj) != target {
                        if ii < i as int {
                            // From outer loop invariant
                        } else {
                            // ii == i as int and jj < j as int
                            assert(ii == i as int);
                            assert(jj < j as int);
                            assert(i as int < jj < j as int); // since ii < jj and ii == i
                            // From inner loop invariant
                        }
                    }
                };
                
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    // When we reach here, no solution was found
    assert(i == n);
    assert(forall|ii: int, jj: int| 0 <= ii < jj < nums.len() ==> nums.spec_index(ii) + nums.spec_index(jj) != target) by {
        forall|ii: int, jj: int| 0 <= ii < jj < nums.len() implies nums.spec_index(ii) + nums.spec_index(jj) != target {
            // Since i == n and we've checked all pairs where the first index is < i
            assert(ii < nums.len());
            assert(ii < n);
            assert(ii < i as int);
            // This follows from the outer loop invariant
        }
    };
    
    return (-1, -1);
}

}