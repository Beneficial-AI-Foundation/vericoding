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

// Helper lemma for sum splitting
proof fn lemma_sum_split(a: Seq<i32>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= a.len()
    ensures sum(a, start, end) == sum(a, start, mid) + sum(a, mid, end)
    decreases end - start
{
    if start >= end {
        // Empty range case - both sides are 0
        assert(sum(a, start, end) == 0);
        assert(sum(a, start, mid) == 0);
        assert(sum(a, mid, end) == 0);
    } else if start == mid {
        // First part is empty
        assert(sum(a, start, mid) == 0);
        assert(sum(a, start, end) == sum(a, mid, end));
    } else if mid == end {
        // Second part is empty  
        assert(sum(a, mid, end) == 0);
        assert(sum(a, start, end) == sum(a, start, mid));
    } else {
        // Recursive case: start < mid < end
        assert(start + 1 <= mid);
        lemma_sum_split(a, start + 1, mid, end);
        
        // From the definition of sum
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, end));
        assert(sum(a, start, mid) == a[start] + sum(a, start + 1, mid));
        
        // From the recursive call
        assert(sum(a, start + 1, end) == sum(a, start + 1, mid) + sum(a, mid, end));
        
        // Substituting
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, mid) + sum(a, mid, end));
        assert(sum(a, start, end) == (a[start] + sum(a, start + 1, mid)) + sum(a, mid, end));
        assert(sum(a, start, end) == sum(a, start, mid) + sum(a, mid, end));
    }
}

// Lemma to help with prefix sum property
proof fn lemma_prefix_sum_property(a: Vec<i32>, c: Vec<i32>, i: int, j: int)
    requires
        0 <= i <= j <= a@.len(),
        is_prefix_sum_for(a, c),
        i < c@.len(),
        j < c@.len()
    ensures
        sum(a@, i, j) == c@[j] - c@[i]
{
    // From is_prefix_sum_for definition
    assert(c@[j] == sum(a@, 0, j));
    assert(c@[i] == sum(a@, 0, i));
    
    // Use the sum splitting lemma to split sum(a@, 0, j) at point i
    lemma_sum_split(a@, 0, i, j);
    
    // The lemma tells us: sum(a@, 0, j) == sum(a@, 0, i) + sum(a@, i, j)
    assert(sum(a@, 0, j) == sum(a@, 0, i) + sum(a@, i, j));
    
    // Substituting the prefix sum values
    assert(c@[j] == c@[i] + sum(a@, i, j));
    
    // Therefore
    assert(sum(a@, i, j) == c@[j] - c@[i]);
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
    // Apply the lemma in proof context
    proof {
        lemma_prefix_sum_property(a, c, i as int, j as int);
    }
    
    // Compute the result
    let ci = c[i];
    let cj = c[j];
    let result = cj - ci;
    
    // Verification that result matches specification
    proof {
        assert(ci == c@[i as int]);
        assert(cj == c@[j as int]);
        assert(result == c@[j as int] - c@[i as int]);
        // The lemma established that sum(a@, i as int, j as int) == c@[j as int] - c@[i as int]
        assert(result == sum(a@, i as int, j as int));
    }
    
    result
}

}