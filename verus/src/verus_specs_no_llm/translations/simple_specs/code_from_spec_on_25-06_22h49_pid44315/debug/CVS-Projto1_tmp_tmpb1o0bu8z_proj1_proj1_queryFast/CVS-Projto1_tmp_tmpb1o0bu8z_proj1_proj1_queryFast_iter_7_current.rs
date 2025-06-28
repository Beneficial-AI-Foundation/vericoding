use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define the sum function that computes sum of elements from index start to end (exclusive)
spec fn sum(a: Seq<int>, start: int, end: int) -> int
    decreases end - start
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
    } else if start == mid {
        // Case where first part is empty
        assert(sum(a, start, mid) == 0);
    } else if mid == end {
        // Case where second part is empty
        assert(sum(a, mid, end) == 0);
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
        0 <= i <= j <= a.len() && 
        a.len() + 1 == c.len() &&
        i < c.len() && j < c.len()
    ensures
        r == sum(a@, i, j)
{
    proof {
        // We need to prove that c[j] - c[i] == sum(a, i, j)
        // From the definition of is_prefix_sum_for:
        
        // First establish that i and j are valid indices for c
        assert(c@.len() == a@.len() + 1);
        assert(0 <= i <= j <= a@.len());
        assert(i < c@.len() && j < c@.len());
        
        // Handle the case when i == 0
        if i == 0 {
            assert(c@[0] == 0) by {
                assert(is_prefix_sum_for(a@, c@));
            };
            if j == 0 {
                assert(sum(a@, 0, 0) == 0);
                assert(c@[0] - c@[0] == 0);
            } else {
                assert(c@[j] == sum(a@, 0, j)) by {
                    assert(is_prefix_sum_for(a@, c@));
                    assert(1 <= j <= a@.len());
                };
                assert(sum(a@, 0, j) == c@[j] - 0);
            }
        } else {
            // Case when i > 0
            assert(c@[j] == sum(a@, 0, j)) by {
                assert(is_prefix_sum_for(a@, c@));
                assert(1 <= j <= a@.len());
            };
            assert(c@[i] == sum(a@, 0, i)) by {
                assert(is_prefix_sum_for(a@, c@));
                assert(1 <= i <= a@.len());
            };
            
            // Use the sum splitting lemma:
            sum_split_lemma(a@, 0, i, j);
            
            // From the lemma: sum(a@, 0, j) == sum(a@, 0, i) + sum(a@, i, j)
            // Therefore: sum(a@, i, j) == sum(a@, 0, j) - sum(a@, 0, i)
            assert(sum(a@, i, j) == c@[j] - c@[i]);
        }
    }
    c[j] - c[i]
}

}