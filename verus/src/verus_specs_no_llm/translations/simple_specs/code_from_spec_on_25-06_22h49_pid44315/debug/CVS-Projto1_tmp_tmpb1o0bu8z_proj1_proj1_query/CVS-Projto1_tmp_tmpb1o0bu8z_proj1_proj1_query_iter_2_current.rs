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
            total == sum(a, i, idx),
            idx <= a.len()
        decreases j - idx
    {
        // Prove that idx is within bounds
        assert(0 <= idx < a.len());
        total = total + a[idx as usize];
        idx = idx + 1;
        
        // Help the prover with the sum relationship
        assert(sum(a, i, idx) == sum(a, i, idx - 1) + a[(idx - 1) as usize]);
    }
    
    return total;
}

}