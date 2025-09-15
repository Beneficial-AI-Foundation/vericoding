// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors for `i` and array indexing. */
{
    let n = nums.len();
    if n < 3 {
        return false;
    }

    let mut min1: i32 = 2147483647; // Represents the smallest first element of a potential triplet
    let mut min2: i32 = 2147483647; // Represents the smallest second element of a potential triplet

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            // These invariants relate to the values min1 and min2 and their existence within the processed part of the array.
            // They ensure that if min1 or min2 are not their initial max value, then there exists an element
            // in nums[0..i] that corresponds to their value, and for min2, an increasing pair exists.
            min1 == 2147483647 || (exists|x:int| 0 <= x < i as int && nums@[x] == min1),
            min2 == 2147483647 || (exists|y:int| 0 <= y < i as int && nums@[y] == min2 && exists|x:int| 0 <= x < y && nums@[x] < nums@[y]),
            // This invariant ensures that min1 is always the smallest element encountered so far if it's not MAX_INT.
            (min1 != 2147483647) ==> 
                (forall|prev_i: int| 0 <= prev_i < i as int ==> nums@[prev_i] >= min1),
            // This invariant states that if min2 is not MAX_INT, there exists a pair (a, b) with a < b < i where
            // nums[a] <= min1 and nums[b] == min2. This ensures min2 is the smallest possible second element
            // of an increasing pair, given the current min1.
            (min2 != 2147483647) ==> 
                (forall|val: i32| (exists|k:int| 0 <= k < i as int && nums@[k] == val && val > min1) ==> val >= min2),
            (min2 != 2147483647) ==> 
                (exists|k1:int, k2:int| 0 <= k1 < k2 < i as int && nums@[k1] <= min1 && nums@[k2] == min2)
    {
        let num = nums@[i]; // Access vector element using 'i as int' for ghost code contexts
        if num <= min1 {
            min1 = num;
        } else if num <= min2 {
            // num > min1
            // This means we found a pair (min1, num)
            // We update min2 to 'num' as it's a smaller second element for a potential subsequence
            min2 = num;
        } else {
            // num > min2 (and num > min1 implicitly)
            // This means we found nums[i] such that nums[i] > min2 > min1
            // We have found an increasing triplet (min1, min2, num)
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}