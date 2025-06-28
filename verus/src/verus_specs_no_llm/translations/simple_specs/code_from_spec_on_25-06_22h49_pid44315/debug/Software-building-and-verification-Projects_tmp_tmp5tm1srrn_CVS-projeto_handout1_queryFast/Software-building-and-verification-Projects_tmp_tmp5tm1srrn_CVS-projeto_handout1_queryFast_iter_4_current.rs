use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define sum function for specification
spec fn sum(a: Seq<i32>, start: int, end: int) -> int
    recommends 0 <= start <= end <= a.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        a[start] + sum(a, start + 1, end)
    }
}

// Define prefix sum property
spec fn is_prefix_sum_for(a: Vec<i32>, c: Vec<i32>) -> bool {
    a@.len() + 1 == c@.len() && 
    forall|i: int| 0 <= i <= a@.len() ==> c@[i] == sum(a@, 0, i)
}

// Lemma to help with prefix sum property
proof fn lemma_prefix_sum_property(a: Vec<i32>, c: Vec<i32>, i: int, j: int)
    requires
        0 <= i <= j <= a@.len(),
        is_prefix_sum_for(a, c)
    ensures
        sum(a@, i, j) == c@[j] - c@[i]
    decreases j - i
{
    if i == j {
        // Base case: empty range
        assert(sum(a@, i, j) == 0);
        assert(c@[j] - c@[i] == c@[i] - c@[i] == 0);
    } else {
        // Inductive case
        lemma_sum_split(a@, 0, i, j);
        assert(sum(a@, 0, j) == sum(a@, 0, i) + sum(a@, i, j));
        assert(c@[j] == sum(a@, 0, j)) by {
            assert(is_prefix_sum_for(a, c));
        }
        assert(c@[i] == sum(a@, 0, i)) by {
            assert(is_prefix_sum_for(a, c));
        }
        assert(sum(a@, i, j) == c@[j] - c@[i]);
    }
}

// Helper lemma for sum splitting
proof fn lemma_sum_split(a: Seq<i32>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= a.len()
    ensures sum(a, start, end) == sum(a, start, mid) + sum(a, mid, end)
    decreases end - start
{
    if start >= end {
        // Empty range
        assert(sum(a, start, end) == 0);
        assert(sum(a, start, mid) == 0);
        assert(sum(a, mid, end) == 0);
    } else if start == mid {
        // First part is empty
        assert(sum(a, start, mid) == 0);
        assert(sum(a, start, end) == sum(a, mid, end));
    } else {
        // Recursive case
        lemma_sum_split(a, start + 1, mid, end);
        assert(sum(a, start + 1, end) == sum(a, start + 1, mid) + sum(a, mid, end));
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, end));
        assert(sum(a, start, mid) == a[start] + sum(a, start + 1, mid));
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, mid) + sum(a, mid, end));
        assert(sum(a, start, end) == sum(a, start, mid) + sum(a, mid, end));
    }
}

fn queryFast(a: Vec<i32>, c: Vec<i32>, i: usize, j: usize) -> (r: i32)
    requires
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a, c),
        i < c.len(),
        j < c.len()
    ensures
        r == sum(a@, i as int, j as int)
{
    proof {
        lemma_prefix_sum_property(a, c, i as int, j as int);
    }
    let result = c[j] - c[i];
    result
}

}