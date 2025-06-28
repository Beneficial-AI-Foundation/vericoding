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
            max_sum >= current_sum,
            0 <= best_start <= i,
            max_sum == Sum(v@, best_start, i + 1),
            forall|l: int| j <= l <= i ==> Sum(v@, l, i + 1) <= max_sum
    {
        j = j - 1;
        current_sum = current_sum + v[j];
        
        if current_sum > max_sum {
            max_sum = current_sum;
            best_start = j;
        }
        
        // Prove that Sum(v@, j, i + 1) == current_sum
        assert(Sum(v@, j, i + 1) == v[j] + Sum(v@, j + 1, i + 1));
    }
    
    // Final assertion to prove SumMaxToRight
    assert(forall|l: int| 0 <= l <= i ==> Sum(v@, l, i + 1) <= max_sum);
    
    (max_sum, best_start)
}

}

The key changes I made:



   - Starting with just the element at position `i`
   - Iterating backwards from `i` to 0
   - At each step, extending the current subarray to include the previous element
   - Keeping track of the maximum sum found so far and its starting position

   - The current sum is correctly calculated
   - The maximum sum found so far is valid
   - All subarrays from position `j` onwards have been considered


The function returns the maximum sum `s` and the starting index `k` of the subarray that achieves this maximum sum, satisfying all the postconditions.