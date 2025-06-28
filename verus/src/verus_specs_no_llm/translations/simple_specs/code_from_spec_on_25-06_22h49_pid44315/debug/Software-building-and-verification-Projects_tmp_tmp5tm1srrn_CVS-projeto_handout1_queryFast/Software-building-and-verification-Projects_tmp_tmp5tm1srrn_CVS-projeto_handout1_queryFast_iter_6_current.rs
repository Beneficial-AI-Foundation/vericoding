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
        // Empty range case
    } else if start == mid {
        // First part is empty
        assert(sum(a, start, mid) == 0);
    } else if mid == end {
        // Second part is empty  
        assert(sum(a, mid, end) == 0);
    } else {
        // Recursive case
        lemma_sum_split(a, start + 1, mid, end);
        // The recursive call establishes:
        // sum(a, start + 1, end) == sum(a, start + 1, mid) + sum(a, mid, end)
        
        // Now we can show the full property
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, end));
        assert(sum(a, start, mid) == a[start] + sum(a, start + 1, mid));
        assert(sum(a, start, end) == a[start] + sum(a, start + 1, mid) + sum(a, mid, end));
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
    decreases j - i
{
    // Use the sum splitting lemma
    lemma_sum_split(a@, 0, i, j);
    
    // From is_prefix_sum_for, we know:
    assert(c@[j] == sum(a@, 0, j));
    assert(c@[i] == sum(a@, 0, i));
    
    // From lemma_sum_split, we know:
    assert(sum(a@, 0, j) == sum(a@, 0, i) + sum(a@, i, j));
    
    // Therefore:
    assert(sum(a@, i, j) == sum(a@, 0, j) - sum(a@, 0, i));
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
    proof {
        // Establish the preconditions for the lemma
        assert(0 <= i as int <= j as int <= a@.len());
        assert(i as int < c@.len());
        assert(j as int < c@.len());
        
        // Apply the lemma
        lemma_prefix_sum_property(a, c, i as int, j as int);
        
        // The lemma gives us what we need
        assert(sum(a@, i as int, j as int) == c@[j as int] - c@[i as int]);
    }
    
    let ci = c[i];
    let cj = c[j];
    let result = cj - ci;
    
    proof {
        // Connect the runtime values to the specification
        assert(ci == c@[i as int]);
        assert(cj == c@[j as int]);
        assert(result == c@[j as int] - c@[i as int]);
        // From the lemma, we know this equals sum(a@, i as int, j as int)
    }
    
    result
}

}