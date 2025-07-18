use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn distinct(nums: Seq<int>) -> bool {
    forall i, j :: 0 <= i < j < nums.len() ==> nums.spec_index(i) != nums.spec_index(j)
}

fn contains_duplicate(nums: Seq<int>) -> (result: bool)
    requires
        1 <= nums.len() <= 100000,
        forall i :: 0 <= i < nums.len() ==> -1000000000 <= nums.spec_index(i) <= 1000000000
    ensures
        result <==> !distinct(nums)
{
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall x, y :: 0 <= x < y < i ==> nums.spec_index(x) != nums.spec_index(y)
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i < nums.len(),
                i + 1 <= j <= nums.len(),
                forall x, y :: 0 <= x < y < i ==> nums.spec_index(x) != nums.spec_index(y),
                forall k :: i + 1 <= k < j ==> nums.spec_index(i) != nums.spec_index(k)
        {
            if nums.spec_index(i) == nums.spec_index(j) {
                assert(!distinct(nums)) by {
                    assert(0 <= i < j < nums.len());
                    assert(nums.spec_index(i) == nums.spec_index(j));
                };
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    assert(distinct(nums)) by {
        assert(forall x, y :: 0 <= x < y < nums.len() ==> nums.spec_index(x) != nums.spec_index(y)) by {
            assert(forall x, y :: 0 <= x < y < nums.len() ==> {
                if x < nums.len() - 1 {
                    // Case where x was checked in outer loop
                    if y > x + 1 {
                        // y was checked against x in inner loop
                        nums.spec_index(x) != nums.spec_index(y)
                    } else {
                        // y = x + 1, was checked in inner loop
                        nums.spec_index(x) != nums.spec_index(y)
                    }
                } else {
                    // x = nums.len() - 1, no duplicates found
                    nums.spec_index(x) != nums.spec_index(y)
                }
            });
        };
    };
    return false;
}

}