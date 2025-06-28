use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j - i
{
    if i >= j {
        0
    } else {
        a[i] + sum(a, i + 1, j)
    }
}

fn query(a: Vec<int>, i: int, j: int) -> (s: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        s == sum(a, i, j)
{
    let mut total = 0;
    let mut idx = i;
    
    while idx < j
        invariant
            i <= idx <= j,
            total == sum(a, i, idx)
        decreases j - idx
    {
        // Since idx < j and j <= a.len(), we have idx < a.len()
        assert(idx < j);
        assert(j <= a.len());
        assert(idx < a.len());
        
        total = total + a[idx];
        
        // Help the prover understand the sum relationship
        // We need to show that sum(a, i, idx + 1) == sum(a, i, idx) + a[idx]
        // Since sum(a, i, idx + 1) = a[i] + sum(a, i + 1, idx + 1)
        // and sum(a, i, idx) = a[i] + sum(a, i + 1, idx) when i < idx
        assert(sum(a, i, idx + 1) == sum(a, i, idx) + a[idx]) by {
            if i == idx {
                // Base case: sum(a, i, i) == 0
                assert(sum(a, i, i) == 0);
                assert(sum(a, i, i + 1) == a[i] + sum(a, i + 1, i + 1));
                assert(sum(a, i + 1, i + 1) == 0);
                assert(sum(a, i, i + 1) == a[i]);
            } else {
                // Recursive case: both sums start with a[i]
                assert(sum(a, i, idx + 1) == a[i] + sum(a, i + 1, idx + 1));
                assert(sum(a, i, idx) == a[i] + sum(a, i + 1, idx));
                // By the recursive structure: sum(a, i+1, idx+1) == sum(a, i+1, idx) + a[idx]
                assert(sum(a, i + 1, idx + 1) == sum(a, i + 1, idx) + a[idx]);
            }
        }
        
        idx = idx + 1;
    }
    
    total
}

}