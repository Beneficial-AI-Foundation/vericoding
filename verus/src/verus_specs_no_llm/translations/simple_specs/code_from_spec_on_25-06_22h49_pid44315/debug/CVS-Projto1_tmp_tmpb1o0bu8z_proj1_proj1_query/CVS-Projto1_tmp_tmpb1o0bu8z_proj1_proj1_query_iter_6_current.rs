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

proof fn lemma_sum_extend(a: Vec<int>, i: int, j: int)
    requires 0 <= i <= j < a.len()
    ensures sum(a, i, j + 1) == sum(a, i, j) + a[j]
    decreases j - i
{
    if i == j {
        assert(sum(a, i, j) == 0);
        assert(sum(a, i, j + 1) == a[i] + sum(a, i + 1, j + 1));
        assert(sum(a, i + 1, j + 1) == 0);
        assert(sum(a, i, j + 1) == a[i]);
        assert(a[j] == a[i]);
    } else {
        assert(sum(a, i, j + 1) == a[i] + sum(a, i + 1, j + 1));
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
        lemma_sum_extend(a, i + 1, j);
        assert(sum(a, i + 1, j + 1) == sum(a, i + 1, j) + a[j]);
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
        assert(idx < j);
        assert(j <= a.len());
        assert(idx < a.len());
        
        total = total + a[idx];
        
        // Use the lemma to prove the sum relationship
        lemma_sum_extend(a, i, idx);
        assert(sum(a, i, idx + 1) == sum(a, i, idx) + a[idx]);
        
        idx = idx + 1;
    }
    
    total
}

}