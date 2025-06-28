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

// Additional helper lemma to prove sum properties
proof fn sum_single_element(v: Seq<int>, i: int)
    requires 0 <= i < v.len()
    ensures Sum(v, i, i + 1) == v[i]
{
    // Follows from definition when l == r - 1
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
    
    // Prove initial conditions
    proof {
        sum_single_element(v@, i);
        assert(Sum(v@, i, i + 1) == v[i]);
    }
    
    let mut j = i;
    while j > 0
        invariant
            0 <= j <= i,
            current_sum == Sum(v@, j, i + 1),
            0 <= best_start <= i,
            max_sum == Sum(v@, best_start, i + 1),
            forall|l: int| j <= l <= i ==> Sum(v@, l, i + 1) <= max_sum,
            max_sum >= current_sum
    {
        j = j - 1;
        
        // Prove the sum extension property before updating current_sum
        proof {
            sum_extend_left(v@, j, i + 1);
            assert(Sum(v@, j, i + 1) == v@[j] + Sum(v@, j + 1, i + 1));
            assert(Sum(v@, j + 1, i + 1) == current_sum);
        }
        
        current_sum = current_sum + v[j];
        
        proof {
            assert(current_sum == Sum(v@, j, i + 1));
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            best_start = j;
            
            proof {
                assert(max_sum == Sum(v@, best_start, i + 1));
                assert(max_sum == Sum(v@, j, i + 1));
            }
        }
        
        proof {
            // Maintain invariant that max_sum is maximum among all considered ranges
            assert(forall|l: int| j <= l <= i ==> Sum(v@, l, i + 1) <= max_sum);
        }
    }
    
    // At this point j == 0, so we've considered all subarrays from 0 to i
    proof {
        assert(j == 0);
        assert(forall|l: int| 0 <= l <= i ==> Sum(v@, l, i + 1) <= max_sum);
        assert(SumMaxToRight(v@, i, max_sum));
        assert(max_sum == Sum(v@, best_start, i + 1));
        assert(0 <= best_start <= i);
    }
    
    (max_sum, best_start)
}

}