use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define the sum function that computes sum of elements from index start to end (exclusive)
spec fn sum(a: Vec<int>, start: int, end: int) -> int
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
spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>) -> bool {
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall|j: int| 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
}

// Fast query function that uses prefix sums to compute range sum
fn queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        is_prefix_sum_for(a, c) && 0 <= i <= j <= a.len() < c.len()
    ensures
        r == sum(a, i, j)
{
    proof {
        // We need to prove that c[j] - c[i] == sum(a, i, j)
        // This follows from the definition of prefix sums
        assert(c[j] == sum(a, 0, j));
        assert(c[i] == sum(a, 0, i));
        
        // Prove that sum(a, 0, j) - sum(a, 0, i) == sum(a, i, j)
        sum_split_lemma(a, 0, i, j);
    }
    c[j] - c[i]
}

// Helper lemma to prove sum splitting property
proof fn sum_split_lemma(a: Vec<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= a.len()
    ensures sum(a, start, end) == sum(a, start, mid) + sum(a, mid, end)
    decreases end - start
{
    if start >= end {
        // Base case: empty range
        assert(sum(a, start, end) == 0);
        assert(sum(a, start, mid) + sum(a, mid, end) == 0 + 0);
    } else if start == mid {
        // Case where first part is empty
        assert(sum(a, start, mid) == 0);
        assert(sum(a, start, end) == sum(a, mid, end));
    } else {
        // Recursive case
        sum_split_lemma(a, start + 1, mid, end);
        assert(sum(a, start + 1, end) == sum(a, start + 1, mid) + sum(a, mid, end));
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, end));
        assert(sum(a, start, mid) == a[start] + sum(a, start + 1, mid));
    }
}

}