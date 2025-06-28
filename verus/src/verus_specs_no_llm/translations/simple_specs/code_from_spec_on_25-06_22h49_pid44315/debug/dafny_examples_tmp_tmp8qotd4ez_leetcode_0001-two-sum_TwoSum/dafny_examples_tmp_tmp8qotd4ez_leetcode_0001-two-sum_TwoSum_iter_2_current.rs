use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TwoSum(nums: Vec<int>, target: int) -> (r: (int, int))
    ensures
        0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() && 
            nums.spec_index(r.0) + nums.spec_index(r.1) == target &&
            forall i, j :: 0 <= i < j < nums.len() && (i < r.0 || (i == r.0 && j < r.1)) ==> nums.spec_index(i) + nums.spec_index(j) != target,
        r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.len() ==> nums.spec_index(i) + nums.spec_index(j) != target
{
    let n = nums.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall ii, jj :: 0 <= ii < jj < nums.len() && (ii < i || (ii == i && jj < i + 1)) ==> nums.spec_index(ii) + nums.spec_index(jj) != target
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i + 1 <= j <= n,
                i < n,
                forall jj :: i + 1 <= jj < j ==> nums.spec_index(i as int) + nums.spec_index(jj) != target,
                forall ii, jj :: 0 <= ii < jj < nums.len() && (ii < i || (ii == i && jj < j)) ==> nums.spec_index(ii) + nums.spec_index(jj) != target
        {
            if nums[i] + nums[j] == target {
                assert(nums.spec_index(i as int) + nums.spec_index(j as int) == target);
                assert(0 <= i as int < j as int < nums.len());
                assert(forall ii, jj :: 0 <= ii < jj < nums.len() && (ii < i as int || (ii == i as int && jj < j as int)) ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    assert(forall ii, jj :: 0 <= ii < jj < nums.len() ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
    return (-1, -1);
}

}