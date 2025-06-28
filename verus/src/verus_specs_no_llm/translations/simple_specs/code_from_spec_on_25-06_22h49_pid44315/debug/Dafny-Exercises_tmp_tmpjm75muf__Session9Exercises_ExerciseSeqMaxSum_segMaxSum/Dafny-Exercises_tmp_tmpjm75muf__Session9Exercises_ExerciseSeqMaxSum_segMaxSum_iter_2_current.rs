use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Sum function to calculate sum of elements from index l to r (exclusive)
spec fn Sum(v: Seq<int>, l: int, r: int) -> int
    decreases r - l
{
    if l >= r {
        0
    } else if l == r - 1 {
        v[l]
    } else {
        v[l] + Sum(v, l + 1, r)
    }
}

// Specification that checks if s is the maximum sum ending at position i
spec fn SumMaxToRight(v: Seq<int>, i: int, s: int) -> bool
{
    forall|l: int| 0 <= l <= i ==> Sum(v, l, i + 1) <= s
}

// Helper lemma for Sum properties
proof fn sum_extend_left(v: Seq<int>, l: int, r: int)
    requires l < r
    ensures Sum(v, l, r) == v[l] + Sum(v, l + 1, r)
{
    // This follows from the definition of Sum
}

// Implementation function
fn segMaxSum(v: Vec<int>, i: int) -> (s: int, k: int)
    requires
        v.len() > 0 && 0 <= i < v.len()
    ensures
        0 <= k <= i && s == Sum(v@, k, i + 1) && SumMaxToRight(v@, i, s)
{
    let mut max_sum = v[i];
    let mut best_start = i;
    let mut current_sum = v[i];
    
    let mut j = i;
    while j > 0
        invariant
            0 <= j <= i,
            current_sum == Sum(v@, j, i + 1),
            0 <= best_start <= i,
            max_sum == Sum(v@, best_start, i + 1),
            forall|l: int| j <= l <= i ==> Sum(v@, l, i + 1) <= max_sum
    {
        j = j - 1;
        
        // Prove the sum extension property before updating current_sum
        proof {
            sum_extend_left(v@, j, i + 1);
        }
        
        current_sum = current_sum + v[j];
        
        if current_sum > max_sum {
            max_sum = current_sum;
            best_start = j;
        }
    }
    
    // At this point j == 0, so we've considered all subarrays from 0 to i
    // The loop invariant gives us: forall|l: int| 0 <= l <= i ==> Sum(v@, l, i + 1) <= max_sum
    // This is exactly what we need for SumMaxToRight
    
    (max_sum, best_start)
}

}

The key fixes I made:





The algorithm works by:
- Starting with the single element at position `i`
- Iterating backwards, extending the current subarray to include previous elements
- Keeping track of the maximum sum found and its starting position
- The loop invariant ensures we've found the maximum among all considered subarrays

When the loop exits with `j == 0`, we've considered all possible subarrays ending at position `i`, and the invariant guarantees that `max_sum` is indeed the maximum sum, satisfying the `SumMaxToRight` postcondition.