use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define the sum function that computes sum of elements from index start to end (exclusive)
spec fn sum(a: Seq<int>, start: int, end: int) -> int
    decreases (if start >= end || start < 0 || end > a.len() { 0 } else { end - start })
{
    if start >= end {
        0
    } else if start < 0 || end > a.len() {
        0
    } else {
        a[start] + sum(a, start + 1, end)
    }
}

// Spec function to check if c is a valid prefix sum array for a
spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool {
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall|j: int| 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
}

// Helper lemma to prove sum splitting property
proof fn sum_split_lemma(a: Seq<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= a.len()
    ensures sum(a, start, end) == sum(a, start, mid) + sum(a, mid, end)
    decreases end - start
{
    if start >= end {
        // Base case: empty range
        assert(sum(a, start, end) == 0);
        assert(sum(a, start, mid) == 0);
        assert(sum(a, mid, end) == 0);
    } else if start == mid {
        // Case where first part is empty
        assert(sum(a, start, mid) == 0);
        assert(sum(a, start, end) == sum(a, mid, end));
    } else if mid == end {
        // Case where second part is empty
        assert(sum(a, mid, end) == 0);
        assert(sum(a, start, end) == sum(a, start, mid));
    } else {
        // Recursive case: start < mid < end
        sum_split_lemma(a, start + 1, mid, end);
        
        // By definition of sum:
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, end));
        assert(sum(a, start, mid) == a[start] + sum(a, start + 1, mid));
        
        // From the inductive hypothesis:
        assert(sum(a, start + 1, end) == sum(a, start + 1, mid) + sum(a, mid, end));
        
        // Combine the results:
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, mid) + sum(a, mid, end));
        assert(sum(a, start, mid) + sum(a, mid, end) == a[start] + sum(a, start + 1, mid) + sum(a, mid, end));
    }
}

// Fast query function that uses prefix sums to compute range sum
fn queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        is_prefix_sum_for(a@, c@) && 
        0 <= i <= j <= a.len()
    ensures
        r == sum(a@, i, j)
{
    proof {
        // From is_prefix_sum_for, we know:
        // - c@.len() == a@.len() + 1
        // - c@[0] == 0
        // - forall k: 1 <= k <= a@.len() ==> c@[k] == sum(a@, 0, k)
        
        assert(c@.len() == a@.len() + 1);
        assert(0 <= i <= j <= a@.len());
        assert(i < c@.len() && j < c@.len());
        
        if i == 0 {
            // When i == 0, we want sum(a@, 0, j)
            assert(c@[0] == 0);
            if j == 0 {
                assert(sum(a@, 0, 0) == 0);
                assert(c@[j] - c@[i] == c@[0] - c@[0] == 0);
            } else {
                // j > 0, so 1 <= j <= a@.len()
                assert(1 <= j <= a@.len());
                assert(c@[j] == sum(a@, 0, j));
                assert(c@[j] - c@[i] == c@[j] - c@[0] == c@[j] - 0 == c@[j]);
                assert(c@[j] == sum(a@, 0, j));
            }
        } else {
            // When i > 0, we have 1 <= i <= j <= a@.len()
            assert(1 <= i <= a@.len());
            assert(1 <= j <= a@.len());
            assert(c@[i] == sum(a@, 0, i));
            assert(c@[j] == sum(a@, 0, j));
            
            // Apply sum splitting lemma
            sum_split_lemma(a@, 0, i, j);
            assert(sum(a@, 0, j) == sum(a@, 0, i) + sum(a@, i, j));
            assert(sum(a@, i, j) == sum(a@, 0, j) - sum(a@, 0, i));
            assert(sum(a@, i, j) == c@[j] - c@[i]);
        }
    }
    
    c[j] - c[i]
}

}